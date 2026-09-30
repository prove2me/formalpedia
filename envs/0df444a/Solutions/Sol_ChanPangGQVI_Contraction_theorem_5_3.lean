-- Prove2me | solution 1 for ChanPangGQVI.Contraction.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:07:35.836215+00:00
-- url     : https://prove2.me/submissions/b74fec3a-0cdf-410a-b6ce-bea5f7cfe1ce

import Mathlib.Topology.MetricSpace.Contracting
import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic
import Definitions.Def_ChanPangGQVI_Contraction_ProjectionMap
set_option autoImplicit false
open ChanPangGQVI.Shared ChanPangGQVI.Contraction
open scoped InnerProductSpace

private theorem nearest_exists {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hne : S.Nonempty) (hc : IsClosed S) (hcv : Convex ℝ S) (z : EuclideanSpace ℝ (Fin n)) :
    ∃ p, IsProj S z p := by
  letI : Nonempty S := hne.to_subtype
  have hb : BddBelow (Set.range (fun y : S => ‖z - y‖)) := ⟨0, by
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _⟩
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv z
  refine ⟨p, hp, ?_⟩
  intro y hy
  rw [norm_sub_rev p z, norm_sub_rev y z, hmin]
  exact ciInf_le hb ⟨y, hy⟩

private theorem proj_spec {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) (he : ∃ p, IsProj S z p) : IsProj S z (proj S z) := by
  classical
  simpa only [proj, dif_pos he] using he.choose_spec

private theorem nearest_inner {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hcv : Convex ℝ S) (z p : EuclideanSpace ℝ (Fin n)) (hp : IsProj S z p) :
    ∀ q ∈ S, inner ℝ (z-p) (q-p) ≤ 0 := by
  letI : Nonempty S := ⟨⟨p,hp.1⟩⟩
  have hb : BddBelow (Set.range (fun y : S => ‖z-y‖)) := ⟨0, by
    rintro _ ⟨y,rfl⟩
    exact norm_nonneg _⟩
  apply (norm_eq_iInf_iff_real_inner_le_zero hcv hp.1).mp
  apply le_antisymm
  · apply le_ciInf
    intro q
    simpa only [norm_sub_rev z p, norm_sub_rev z q] using hp.2 q q.2
  · exact ciInf_le hb ⟨p,hp.1⟩

private theorem nearest_unique {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hcv : Convex ℝ S) (z p q : EuclideanSpace ℝ (Fin n))
    (hp : IsProj S z p) (hq : IsProj S z q) : p=q := by
  have h1 := nearest_inner S hcv z p hp q hq.1
  have h2 := nearest_inner S hcv z q hq p hp.1
  have hh : inner ℝ (p-q) (p-q) ≤ 0 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm q p] at *
    linarith
  have hn : ‖p-q‖=0 := by
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

private theorem proj_translate {n : ℕ}
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n)))
    (hK_ne : Ktil.Nonempty) (hK_closed : IsClosed Ktil) (hK_convex : Convex ℝ Ktil)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.proj (Kmap m Ktil x) y =
      m x + ChanPangGQVI.Shared.proj Ktil (y - m x) := by
  have hp := proj_spec Ktil (y-m x) (nearest_exists Ktil hK_ne hK_closed hK_convex (y-m x))
  have he : ∃ q, IsProj (Kmap m Ktil x) y q := by
    refine ⟨m x + proj Ktil (y-m x), ⟨_, hp.1, rfl⟩, ?_⟩
    rintro q ⟨k,hk,rfl⟩
    have hid (a : EuclideanSpace ℝ (Fin n)) : m x + a - y = a - (y-m x) := by abel
    rw [hid, hid]
    exact hp.2 k hk
  have hq := proj_spec (Kmap m Ktil x) y he
  have hback : IsProj Ktil (y-m x) (proj (Kmap m Ktil x) y - m x) := by
    constructor
    · obtain ⟨k,hk,hkeq⟩ := hq.1
      rw [hkeq]
      simpa using hk
    · intro k hk
      have h := hq.2 (m x+k) ⟨k,hk,rfl⟩
      have hleft : proj (Kmap m Ktil x) y - m x - (y-m x) = proj (Kmap m Ktil x) y - y := by abel
      have hright : k - (y-m x) = m x+k-y := by abel
      simpa only [hleft, hright] using h
  have hh := nearest_unique Ktil hK_convex (y-m x) _ _ hback hp
  rw [← hh]
  abel

private theorem proj_nonexpansive {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hne : S.Nonempty) (hc : IsClosed S) (hcv : Convex ℝ S) (z w : EuclideanSpace ℝ (Fin n)) :
    ‖proj S z - proj S w‖ ≤ ‖z-w‖ := by
  have hp := proj_spec S z (nearest_exists S hne hc hcv z)
  have hq := proj_spec S w (nearest_exists S hne hc hcv w)
  have h1 := nearest_inner S hcv z _ hp _ hq.1
  have h2 := nearest_inner S hcv w _ hq _ hp.1
  have hh : inner ℝ (proj S z-proj S w) (proj S z-proj S w) ≤
      inner ℝ (z-w) (proj S z-proj S w) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm (proj S w) (proj S z)] at *
    linarith
  have hb := real_inner_le_norm (z-w) (proj S z-proj S w)
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (proj S z-proj S w), norm_nonneg (z-w)]

private theorem lipschitz_bound {n : ℕ}
    (m f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n)))
    (hK_ne : Ktil.Nonempty) (hK_closed : IsClosed Ktil) (hK_convex : Convex ℝ Ktil)
    (α β γ δ : ℝ)
    (hm_lip : ∀ x y, ‖m x - m y‖ ≤ α * ‖x - y‖)
    (hf_lip : ∀ x y, ‖f x - f y‖ ≤ β * ‖x - y‖)
    (hf_mono : ∀ x y, δ * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (f x - f y))
    (hm_mono : ∀ x y, γ * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (m x - m y))
    (lam : ℝ) (hlam : 0 < lam) (y₁ y₂ : EuclideanSpace ℝ (Fin n)) :
    ‖Flam m f Ktil lam y₁ - Flam m f Ktil lam y₂‖ ≤
      (α + Real.sqrt (lam ^ 2 * β ^ 2 + 2 * lam * (α * β - δ) + (1 + α ^ 2 - 2 * γ))) *
        ‖y₁ - y₂‖ := by
  by_cases hxy : y₁=y₂
  · subst y₂
    simp
  have hd : 0 < ‖y₁-y₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hm := hm_lip y₁ y₂
  have hf := hf_lip y₁ y₂
  have ham : 0 ≤ α * ‖y₁-y₂‖ := (norm_nonneg _).trans hm
  have hbf : 0 ≤ β * ‖y₁-y₂‖ := (norm_nonneg _).trans hf
  have hm2 : ‖m y₁-m y₂‖^2 ≤ (α*‖y₁-y₂‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hf2 : ‖f y₁-f y₂‖^2 ≤ (β*‖y₁-y₂‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
  have hmf : inner ℝ (m y₁-m y₂) (f y₁-f y₂) ≤ (α*‖y₁-y₂‖)*(β*‖y₁-y₂‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul hm hf (norm_nonneg _) ham)
  let Q := lam ^ 2 * β ^ 2 + 2 * lam * (α * β - δ) + (1 + α ^ 2 - 2 * γ)
  let Z := (y₁-y₂)-(m y₁-m y₂)-lam • (f y₁-f y₂)
  have hzsq : ‖Z‖^2 ≤ Q * ‖y₁-y₂‖^2 := by
    have hex : ‖Z‖^2 = ‖y₁-y₂‖^2 + ‖m y₁-m y₂‖^2 + lam^2*‖f y₁-f y₂‖^2
        - 2*inner ℝ (y₁-y₂) (m y₁-m y₂) - 2*lam*inner ℝ (y₁-y₂) (f y₁-f y₂)
        + 2*lam*inner ℝ (m y₁-m y₂) (f y₁-f y₂) := by
      simp only [Z, norm_sub_sq_real, inner_sub_left, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hwf := mul_le_mul_of_nonneg_left hf2 (sq_nonneg lam)
    have hwfm := mul_le_mul_of_nonneg_left (hf_mono y₁ y₂) (by positivity : 0 ≤ 2*lam)
    have hwmm := hm_mono y₁ y₂
    have hwmf := mul_le_mul_of_nonneg_left hmf (by positivity : 0 ≤ 2*lam)
    dsimp [Q]
    nlinarith
  have hQ : 0 ≤ Q := nonneg_of_mul_nonneg_left ((sq_nonneg ‖Z‖).trans hzsq) (sq_pos_of_pos hd)
  have hz : ‖Z‖ ≤ Real.sqrt Q * ‖y₁-y₂‖ := by
    have hs : (Real.sqrt Q * ‖y₁-y₂‖)^2 = Q * ‖y₁-y₂‖^2 := by rw [mul_pow, Real.sq_sqrt hQ]
    have hs0 : 0 ≤ Real.sqrt Q * ‖y₁-y₂‖ := mul_nonneg (Real.sqrt_nonneg _) hd.le
    nlinarith [norm_nonneg Z]
  unfold Flam
  rw [proj_translate m Ktil hK_ne hK_closed hK_convex y₁,
    proj_translate m Ktil hK_ne hK_closed hK_convex y₂]
  have he : m y₁ + proj Ktil (y₁-lam • f y₁-m y₁) - (m y₂ + proj Ktil (y₂-lam • f y₂-m y₂)) =
      (m y₁-m y₂) + (proj Ktil (y₁-lam • f y₁-m y₁) - proj Ktil (y₂-lam • f y₂-m y₂)) := by abel
  rw [he]
  have hzid : (y₁-lam • f y₁-m y₁)-(y₂-lam • f y₂-m y₂) = Z := by
    dsimp [Z]
    simp only [smul_sub]
    abel
  have hp := proj_nonexpansive Ktil hK_ne hK_closed hK_convex
    (y₁-lam • f y₁-m y₁) (y₂-lam • f y₂-m y₂)
  rw [hzid] at hp
  calc
    _ ≤ ‖m y₁-m y₂‖ + ‖proj Ktil (y₁-lam • f y₁-m y₁) - proj Ktil (y₂-lam • f y₂-m y₂)‖ := norm_add_le _ _
    _ ≤ α*‖y₁-y₂‖ + Real.sqrt Q * ‖y₁-y₂‖ := add_le_add hm (hp.trans hz)
    _ = _ := by dsimp [Q]; ring

open Filter
open scoped Topology NNReal

theorem solution {n : ℕ}
    (m f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n)))
    (hK_ne : Ktil.Nonempty) (hK_closed : IsClosed Ktil) (hK_convex : Convex ℝ Ktil)
    (α β γ δ : ℝ)
    (hm_lip : ∀ x y, ‖m x - m y‖ ≤ α * ‖x - y‖)
    (hf_lip : ∀ x y, ‖f x - f y‖ ≤ β * ‖x - y‖)
    (hf_mono : ∀ x y, δ * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (f x - f y))
    (hm_mono : ∀ x y, γ * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (m x - m y))
    (lam : ℝ) (hlam : 0 < lam)
    (hlam_cond : lam ^ 2 * β ^ 2 + 2 * lam * (α * β - δ) - 2 * (γ - α) < 0) :
    (∃ c : ℝ≥0, ContractingWith c (Flam m f Ktil lam)) ∧
      ∃ xt : EuclideanSpace ℝ (Fin n),
        Flam m f Ktil lam xt = xt ∧
        ChanPangGQVI.Shared.IsGQVISolution (Kmap m Ktil) (fun z => {f z}) xt (f xt) ∧
        ∀ x0 : EuclideanSpace ℝ (Fin n),
          Tendsto (fun k : ℕ => (Flam m f Ktil lam)^[k] x0) atTop (𝓝 xt) := by
  classical
  have hc : ∃ c : ℝ≥0, ContractingWith c (Flam m f Ktil lam) := by
    rcases subsingleton_or_nontrivial (EuclideanSpace ℝ (Fin n)) with hs | hn
    · letI := hs
      refine ⟨0, by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
      intro x y
      simp [Subsingleton.elim (Flam m f Ktil lam x) (Flam m f Ktil lam y)]
    · letI := hn
      obtain ⟨x,y,hxy⟩ := exists_pair_ne (EuclideanSpace ℝ (Fin n))
      have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hα : 0 ≤ α := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hm_lip x y)) hd
      have hβ : 0 ≤ β := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf_lip x y)) hd
      have hγ : γ ≤ α := by
        have h1 := hm_mono x y
        have h2 := real_inner_le_norm (x-y) (m x-m y)
        have h3 := mul_le_mul_of_nonneg_left (hm_lip x y) hd.le
        have h4 : γ * ‖x-y‖^2 ≤ α * ‖x-y‖^2 := by nlinarith
        exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp (by simpa only [mul_comm] using h4)
      have hδ : δ ≤ β := by
        have h1 := hf_mono x y
        have h2 := real_inner_le_norm (x-y) (f x-f y)
        have h3 := mul_le_mul_of_nonneg_left (hf_lip x y) hd.le
        have h4 : δ * ‖x-y‖^2 ≤ β * ‖x-y‖^2 := by nlinarith
        exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp (by simpa only [mul_comm] using h4)
      have hαlt : α < 1 := by
        by_contra hbad
        have ha1 : 1 ≤ α := le_of_not_gt hbad
        have hcross : 0 ≤ α*β-δ := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hβ]
        have hp := mul_nonneg (by positivity : 0 ≤ 2*lam) hcross
        nlinarith [mul_nonneg (sq_nonneg lam) (sq_nonneg β)]
      let Q := lam ^ 2 * β ^ 2 + 2 * lam * (α * β - δ) + (1 + α ^ 2 - 2 * γ)
      have hsqrt : Real.sqrt Q < 1-α := (Real.sqrt_lt' (sub_pos.mpr hαlt)).mpr (by dsimp [Q]; nlinarith)
      let c : ℝ≥0 := ⟨α+Real.sqrt Q, add_nonneg hα (Real.sqrt_nonneg _)⟩
      refine ⟨c, ?_, LipschitzWith.of_dist_le_mul ?_⟩
      · change α+Real.sqrt Q < 1
        linarith
      · intro u v
        rw [dist_eq_norm, dist_eq_norm]
        change ‖Flam m f Ktil lam u - Flam m f Ktil lam v‖ ≤ (α+Real.sqrt Q)*‖u-v‖
        exact lipschitz_bound m f Ktil hK_ne hK_closed hK_convex
          α β γ δ hm_lip hf_lip hf_mono hm_mono lam hlam u v
  obtain ⟨c,hc⟩ := hc
  let xt := hc.fixedPoint (Flam m f Ktil lam)
  have hfix : Flam m f Ktil lam xt = xt := hc.fixedPoint_isFixedPt
  refine ⟨⟨c,hc⟩,xt,hfix,?_,?_⟩
  · have hp := proj_spec Ktil (xt-lam • f xt-m xt)
      (nearest_exists Ktil hK_ne hK_closed hK_convex (xt-lam • f xt-m xt))
    have hx : xt = m xt + proj Ktil (xt-lam • f xt-m xt) := by
      calc xt = Flam m f Ktil lam xt := hfix.symm
           _ = _ := proj_translate m Ktil hK_ne hK_closed hK_convex xt (xt-lam • f xt)
    refine ⟨⟨_, hp.1, hx⟩, rfl, ?_⟩
    rintro q ⟨k,hk,hq⟩
    have hi := nearest_inner Ktil hK_convex (xt-lam • f xt-m xt) _ hp k hk
    have hvec : xt-lam • f xt-m xt-proj Ktil (xt-lam • f xt-m xt) = -lam • f xt := by
      calc
        _ = xt-(m xt+proj Ktil (xt-lam • f xt-m xt))-lam • f xt := by module
        _ = -lam • f xt := by rw [← hx]; module
    have hdisp : k-proj Ktil (xt-lam • f xt-m xt) = q-xt := by
      calc
        _ = (m xt+k)-(m xt+proj Ktil (xt-lam • f xt-m xt)) := by abel
        _ = q-xt := by rw [← hq, ← hx]
    rw [hvec, hdisp, real_inner_smul_left] at hi
    have hcomm : inner ℝ (f xt) (q-xt) = inner ℝ (q-xt) (f xt) := real_inner_comm _ _
    nlinarith
  · intro x0
    exact hc.tendsto_iterate_fixedPoint x0
