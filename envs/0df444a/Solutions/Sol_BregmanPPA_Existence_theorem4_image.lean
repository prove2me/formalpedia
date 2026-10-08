-- Prove2me | solution 1 for BregmanPPA.Existence.theorem4_image
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T17:27:25.667946+00:00
-- url     : https://prove2.me/submissions/48b41f91-f58e-4826-81cf-59fc0fd27ba3

import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_Existence_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Mathlib
set_option autoImplicit false
section

open InnerProductSpace ThreeOpSplitting.Convergence
open Filter Topology

namespace DouglasRachfordPPA.GenDR

lemma gdr_g_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a b x : H) :
    ⟪x - a, x - b⟫_ℝ = ‖x - (1/2:ℝ) • (a + b)‖ ^ 2 - ‖(1/2:ℝ) • (a - b)‖ ^ 2 := by
  have h1 : x - a = (x - (1/2:ℝ) • (a + b)) - (1/2:ℝ) • (a - b) := by module
  have h2 : x - b = (x - (1/2:ℝ) • (a + b)) + (1/2:ℝ) • (a - b) := by module
  rw [h1, h2, inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm (x - (1/2:ℝ) • (a + b))]
  ring

lemma gdr_g_pert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a b x d : H) (t : ℝ) :
    ⟪(x - t • d) - a, (x - t • d) - b⟫_ℝ = ⟪x - a, x - b⟫_ℝ
      - 2 * t * ⟪x - (1/2:ℝ) • (a + b), d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2 := by
  rw [gdr_g_eq, gdr_g_eq]
  have : x - t • d - (1/2:ℝ) • (a + b) = (x - (1/2:ℝ) • (a + b)) - t • d := by module
  rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Weighted inequality: the key algebraic step. -/
lemma gdr_weighted {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (a b : ι → H) (hmono : ∀ i j, 0 ≤ ⟪a i - a j, b j - b i⟫_ℝ) :
    ∑ i, w i * ⟪(∑ j, w j • ((1/2:ℝ) • (a j + b j))) - a i,
        (∑ j, w j • ((1/2:ℝ) • (a j + b j))) - b i⟫_ℝ ≤ 0 := by
  set A := ∑ j, w j • a j
  set B := ∑ j, w j • b j
  have hx : ∑ j, w j • ((1/2:ℝ) • (a j + b j)) = (1/2:ℝ) • (A + B) := by
    simp only [A, B, Finset.smul_sum, ← Finset.sum_add_distrib, smul_add, smul_comm (w _) (1/2:ℝ)]
  rw [hx]
  set x := (1/2:ℝ) • (A + B)
  have e1 : ∀ i, ⟪x - a i, x - b i⟫_ℝ = ‖x‖^2 - ⟪x, b i⟫_ℝ - ⟪a i, x⟫_ℝ + ⟪a i, b i⟫_ℝ := by
    intro i
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq]; ring
  simp_rw [e1]
  have hs : ∑ i, w i * (‖x‖^2 - ⟪x, b i⟫_ℝ - ⟪a i, x⟫_ℝ + ⟪a i, b i⟫_ℝ)
      = ‖x‖^2 - ⟪x, B⟫_ℝ - ⟪A, x⟫_ℝ + ∑ i, w i * ⟪a i, b i⟫_ℝ := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hw1, one_mul, A, B, inner_sum, sum_inner, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [hs]
  -- double sum
  have hD : 0 ≤ ∑ i, ∑ j, w i * w j * ⟪a i - a j, b j - b i⟫_ℝ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hw0 i) (hw0 j)) (hmono i j)
  have hAB : ⟪A, B⟫_ℝ = ∑ i, ∑ j, w i * w j * ⟪a i, b j⟫_ℝ := by
    simp only [A, B, sum_inner, inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have hBA : ⟪A, B⟫_ℝ = ∑ i, ∑ j, w i * w j * ⟪a j, b i⟫_ℝ := by
    rw [hAB, Finset.sum_comm]; simp only [mul_comm (w _) (w _)]
  have hd1 : ∑ i, ∑ j, w i * w j * ⟪a i, b i⟫_ℝ = ∑ i, w i * ⟪a i, b i⟫_ℝ := by
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_mul, ← Finset.mul_sum, hw1, mul_one]
  have hd2 : ∑ i, ∑ j, w i * w j * ⟪a j, b j⟫_ℝ = ∑ i, w i * ⟪a i, b i⟫_ℝ := by
    rw [Finset.sum_comm]; simp only [mul_comm (w _) (w _)]; exact hd1
  have hexp : ∑ i, ∑ j, w i * w j * ⟪a i - a j, b j - b i⟫_ℝ =
      (∑ i, ∑ j, w i * w j * ⟪a i, b j⟫_ℝ) - (∑ i, ∑ j, w i * w j * ⟪a i, b i⟫_ℝ)
      - (∑ i, ∑ j, w i * w j * ⟪a j, b j⟫_ℝ) + (∑ i, ∑ j, w i * w j * ⟪a j, b i⟫_ℝ) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  rw [hexp, ← hAB, ← hBA, hd1, hd2] at hD
  have hx2 : ‖x‖^2 = (1/4:ℝ) * (‖A‖^2 + 2 * ⟪A, B⟫_ℝ + ‖B‖^2) := by
    simp only [x, norm_smul, mul_pow, norm_add_sq_real]; norm_num
  have hxB : ⟪x, B⟫_ℝ = (1/2:ℝ) * (⟪A, B⟫_ℝ + ‖B‖^2) := by
    simp only [x, inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
  have hAx : ⟪A, x⟫_ℝ = (1/2:ℝ) * (‖A‖^2 + ⟪A, B⟫_ℝ) := by
    simp only [x, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
  have hAmB : 0 ≤ ‖A - B‖^2 := sq_nonneg _
  rw [norm_sub_sq_real] at hAmB
  rw [hx2, hxB, hAx]
  nlinarith


/-- projection variational inequality onto a compact convex set -/
lemma gdr_proj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Set H) (hK : Convex ℝ K) (x q : H) (hq : q ∈ K)
    (hmin : ∀ y ∈ K, ‖x - q‖ ≤ ‖x - y‖) : ∀ z ∈ K, ⟪x - q, z - q⟫_ℝ ≤ 0 := by
  intro z hz
  by_contra hcon
  push_neg at hcon
  set ε := ⟪x - q, z - q⟫_ℝ
  set N := ‖z - q‖ ^ 2
  have hN : 0 ≤ N := sq_nonneg _
  set t := min 1 (ε / (N + 1))
  have ht0 : 0 < t := lt_min one_pos (div_pos hcon (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ ε / (N + 1) := min_le_right _ _
  have htN : t * N < 2 * ε := by
    have : t * (N + 1) ≤ ε := by rwa [le_div_iff₀ (by linarith)] at ht2
    nlinarith
  have hmem : q + t • (z - q) ∈ K := by
    have := hK hq hz (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    convert this using 1; module
  have h1 := hmin _ hmem
  have h2 : ‖x - (q + t • (z - q))‖ ^ 2 = ‖x - q‖ ^ 2 - 2 * t * ε + t ^ 2 * N := by
    have : x - (q + t • (z - q)) = (x - q) - t • (z - q) := by module
    rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h3 : ‖x - q‖ ^ 2 ≤ ‖x - (q + t • (z - q))‖ ^ 2 := by
    gcongr
  rw [h2] at h3
  nlinarith

lemma gdr_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset (H × H)) (hs : s.Nonempty)
    (hmono : ∀ p ∈ s, ∀ q ∈ s, 0 ≤ ⟪p.1 - q.1, q.2 - p.2⟫_ℝ) :
    ∃ x : H, ∀ p ∈ s, ⟪x - p.1, x - p.2⟫_ℝ ≤ 0 := by
  classical
  set cen : H × H → H := fun p => (1/2:ℝ) • (p.1 + p.2) with hcen
  set g : H × H → H → ℝ := fun p x => ⟪x - p.1, x - p.2⟫_ℝ with hg
  have gcont : ∀ p, Continuous (g p) := fun p => by
    simp only [hg]; fun_prop
  set K := convexHull ℝ (cen '' (s : Set (H × H)))
  have hKc : IsCompact K := (s.finite_toSet.image cen).isCompact_convexHull ℝ
  obtain ⟨p0, hp0⟩ := hs
  have hKne : K.Nonempty := ⟨cen p0, subset_convexHull ℝ _ ⟨p0, hp0, rfl⟩⟩
  set φ : H → ℝ := fun x => s.sup' ⟨p0, hp0⟩ (fun p => g p x)
  have hφc : Continuous φ := Continuous.finset_sup'_apply _ (fun p _ => gcont p)
  obtain ⟨xs, hxsK, hxmin⟩ := hKc.exists_isMinOn hKne hφc.continuousOn
  set m := φ xs
  have hgm : ∀ p ∈ s, g p xs ≤ m := fun p hp => Finset.le_sup' (fun p => g p xs) hp
  suffices hm : m ≤ 0 from ⟨xs, fun p hp => (hgm p hp).trans hm⟩
  set I := s.filter (fun p => g p xs = m)
  have hIs : I ⊆ s := Finset.filter_subset _ _
  obtain ⟨pm, hpm, hpmeq⟩ := Finset.exists_mem_eq_sup' ⟨p0, hp0⟩ (fun p => g p xs)
  have hpmI : pm ∈ I := Finset.mem_filter.2 ⟨hpm, hpmeq.symm⟩
  set KI := convexHull ℝ (cen '' (I : Set (H × H)))
  have hKIK : KI ⊆ K := convexHull_mono (Set.image_mono (by exact_mod_cast hIs))
  have hxsKI : xs ∈ KI := by
    by_contra hnot
    have hKIc : IsCompact KI := (I.finite_toSet.image cen).isCompact_convexHull ℝ
    have hKIne : KI.Nonempty := ⟨cen pm, subset_convexHull ℝ _ ⟨pm, hpmI, rfl⟩⟩
    obtain ⟨q, hqKI, hqmin⟩ := hKIc.exists_isMinOn hKIne
      (continuous_const.sub continuous_id).norm.continuousOn (f := fun y => ‖xs - y‖)
    have hvi := gdr_proj KI (convex_convexHull ℝ _) xs q hqKI (fun y hy => hqmin hy)
    set d := xs - q
    have hd : d ≠ 0 := by
      intro h; apply hnot; rw [show xs = q from sub_eq_zero.1 h]; exact hqKI
    have hdpos : 0 < ‖d‖ ^ 2 := by positivity
    have hact : ∀ p ∈ I, ‖d‖ ^ 2 ≤ ⟪xs - cen p, d⟫_ℝ := by
      intro p hp
      have := hvi (cen p) (subset_convexHull ℝ _ ⟨p, hp, rfl⟩)
      have e : xs - cen p = d - (cen p - q) := by simp only [d]; abel
      rw [e, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
      linarith
    -- find t
    have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
        0 < t ∧ t ≤ 1 ∧ ∀ p ∈ s, p ∉ I → g p (xs - t • d) < m := by
      refine (Filter.Eventually.and self_mem_nhdsWithin ?_)
      refine Filter.Eventually.and ?_ ?_
      · exact nhdsWithin_le_nhds (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
      · rw [Filter.eventually_all_finset]
        intro p hp
        by_cases hpI : p ∈ I
        · exact Filter.Eventually.of_forall fun _ h => absurd hpI h
        · have hlt : g p xs < m := by
            refine lt_of_le_of_ne (hgm p hp) ?_
            intro h; exact hpI (Finset.mem_filter.2 ⟨hp, h⟩)
          have hc : Continuous (fun t : ℝ => g p (xs - t • d)) :=
            (gcont p).comp (continuous_const.sub (continuous_id.smul continuous_const))
          have ht := hc.tendsto 0
          simp only [zero_smul, sub_zero] at ht
          exact nhdsWithin_le_nhds ((ht.eventually (gt_mem_nhds hlt)).mono fun _ h _ => h)
    obtain ⟨t, ht0, ht1, htI⟩ := hev.exists
    have hmemK : xs - t • d ∈ K := by
      have := (convex_convexHull ℝ (cen '' (s : Set (H × H)))) hxsK (hKIK hqKI)
        (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
      convert this using 1; simp only [d]; module
    have hlt : φ (xs - t • d) < m := by
      obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup' ⟨p0, hp0⟩ (fun p => g p (xs - t • d))
      show s.sup' _ (fun p => g p (xs - t • d)) < m
      rw [hpeq]
      by_cases hpI : p ∈ I
      · have hgp : g p xs = m := (Finset.mem_filter.1 hpI).2
        have := gdr_g_pert p.1 p.2 xs d t
        have ha := hact p hpI
        simp only [hg] at hgp ⊢
        rw [this, hgp]
        have : 0 < t * ‖d‖ ^ 2 * (2 - t) :=
          mul_pos (mul_pos ht0 hdpos) (by linarith)
        nlinarith
      · exact htI p hp hpI
    exact absurd (hxmin hmemK) (not_le.2 hlt)
  -- now xs is a convex combination of active centers
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hxs⟩ := mem_convexHull_iff_exists_fintype.1 hxsKI
  choose pz hpzI hpzc using fun i => (hz i)
  have key := gdr_weighted w hw0 hw1 (fun i => (pz i).1) (fun i => (pz i).2)
    (fun i j => hmono _ (hIs (hpzI i)) _ (hIs (hpzI j)))
  have hxs' : ∑ j, w j • ((1/2:ℝ) • ((pz j).1 + (pz j).2)) = xs := by
    rw [← hxs]; apply Finset.sum_congr rfl; intro j _; rw [← hpzc j]
  rw [hxs'] at key
  have hall : ∀ i, ⟪xs - (pz i).1, xs - (pz i).2⟫_ℝ = m := fun i =>
    (Finset.mem_filter.1 (hpzI i)).2
  simp only [hall, ← Finset.sum_mul, hw1, one_mul] at key
  exact key

lemma gdr_real_ulim {ι : Type*} (f : ι → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) (U : Ultrafilter ι) :
    ∃ a, Tendsto f U (𝓝 a) := by
  have hc : IsCompact (Set.Icc (-M) M) := isCompact_Icc
  obtain ⟨a, -, ha⟩ := hc.ultrafilter_le_nhds (U.map f) (by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.univ_mem' (fun k => abs_le.1 (hM k)))
  exact ⟨a, ha⟩

lemma gdr_exists_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (u : ι → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (U : Ultrafilter ι) :
    ∃ w : H, ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y)) := by
  have hb : ∀ y k, |inner ℝ (u k) y| ≤ M * ‖y‖ := fun y k =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
  have hex : ∀ y, ∃ a, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 a) :=
    fun y => gdr_real_ulim _ _ (hb y) U
  set L : H → ℝ := fun y => limUnder (U : Filter ι) (fun k => inner ℝ (u k) y) with hL
  have hLt : ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (L y)) :=
    fun y => tendsto_nhds_limUnder (hex y)
  have hadd : ∀ y y', L (y + y') = L y + L y' := by
    intro y y'
    have h1 := hLt (y + y')
    have h2 := (hLt y).add (hLt y')
    simp only [inner_add_right] at h1
    exact tendsto_nhds_unique h1 h2
  have hsmul : ∀ (c : ℝ) y, L (c • y) = c * L y := by
    intro c y
    have h1 := hLt (c • y)
    have h2 := (hLt y).const_mul c
    simp only [real_inner_smul_right] at h1
    exact tendsto_nhds_unique h1 h2
  let Ll : H →ₗ[ℝ] ℝ :=
    { toFun := L, map_add' := hadd, map_smul' := fun c y => by simp [hsmul] }
  have hbd : ∀ y, ‖Ll y‖ ≤ M * ‖y‖ := by
    intro y
    show |L y| ≤ M * ‖y‖
    have := (hLt y)
    have hmem : ∀ᶠ k in (U : Filter ι), inner ℝ (u k) y ∈ Set.Icc (-(M * ‖y‖)) (M * ‖y‖) :=
      Filter.Eventually.of_forall (fun k => abs_le.1 (hb y k))
    exact abs_le.2 (isClosed_Icc.mem_of_tendsto this hmem)
  let Lc : StrongDual ℝ H := Ll.mkContinuous M hbd
  refine ⟨(InnerProductSpace.toDual ℝ H).symm Lc, fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hLt y

lemma gdr_weak_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : Type*} (U : Filter ι) [U.NeBot] (u : ι → H) (w a b : H)
    (hw : ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y)))
    (hev : ∀ᶠ k in U, ⟪u k - a, u k - b⟫_ℝ ≤ 0) : ⟪w - a, w - b⟫_ℝ ≤ 0 := by
  set c := (1/2:ℝ) • (a + b)
  set r := ‖(1/2:ℝ) • (a - b)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hev2 : ∀ᶠ k in U, ⟪u k - c, w - c⟫_ℝ ≤ r * ‖w - c‖ := by
    filter_upwards [hev] with k hk
    rw [gdr_g_eq] at hk
    have h1 : ‖u k - c‖ ≤ r := by
      have : ‖u k - c‖ ^ 2 ≤ r ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).1 this
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  have hlim : Tendsto (fun k => ⟪u k - c, w - c⟫_ℝ) U (𝓝 (‖w - c‖ ^ 2)) := by
    have := (hw (w - c)).sub (tendsto_const_nhds (x := ⟪c, w - c⟫_ℝ))
    simp only [← inner_sub_left, real_inner_self_eq_norm_sq] at this
    exact this
  have hle : ‖w - c‖ ^ 2 ≤ r * ‖w - c‖ := le_of_tendsto hlim hev2
  have hle2 : ‖w - c‖ ≤ r := by
    by_contra h; push_neg at h
    have : 0 < ‖w - c‖ := lt_of_le_of_lt hr h
    nlinarith
  rw [gdr_g_eq]
  have := norm_nonneg (w - c)
  nlinarith

lemma gdr_inf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : Set (H × H)) (hmono : ∀ p ∈ S, ∀ q ∈ S, 0 ≤ ⟪p.1 - q.1, q.2 - p.2⟫_ℝ) :
    ∃ x : H, ∀ p ∈ S, ⟪x - p.1, x - p.2⟫_ℝ ≤ 0 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨p0, hp0⟩
  · exact ⟨0, fun p hp => by simp [hS] at hp⟩
  set F' : Finset (H × H) → Finset (H × H) := fun F => insert p0 (F.filter (· ∈ S))
  have hF'S : ∀ F, ∀ p ∈ F' F, p ∈ S := by
    intro F p hp
    rcases Finset.mem_insert.1 hp with h | h
    · rw [h]; exact hp0
    · exact (Finset.mem_filter.1 h).2
  have hex : ∀ F, ∃ x : H, ∀ p ∈ F' F, ⟪x - p.1, x - p.2⟫_ℝ ≤ 0 := fun F =>
    gdr_finite (F' F) ⟨p0, Finset.mem_insert_self _ _⟩
      (fun p hp q hq => hmono p (hF'S F p hp) q (hF'S F q hq))
  choose xF hxF using hex
  set c0 := (1/2:ℝ) • (p0.1 + p0.2)
  set r0 := ‖(1/2:ℝ) • (p0.1 - p0.2)‖
  have hbd : ∀ F, ‖xF F‖ ≤ ‖c0‖ + r0 := by
    intro F
    have h := hxF F p0 (Finset.mem_insert_self _ _)
    rw [gdr_g_eq] at h
    have h1 : ‖xF F - c0‖ ≤ r0 := by
      have : ‖xF F - c0‖ ^ 2 ≤ r0 ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    calc ‖xF F‖ = ‖(xF F - c0) + c0‖ := by rw [sub_add_cancel]
      _ ≤ ‖xF F - c0‖ + ‖c0‖ := norm_add_le _ _
      _ ≤ ‖c0‖ + r0 := by linarith
  set U : Ultrafilter (Finset (H × H)) := Ultrafilter.of (atTop : Filter (Finset (H × H)))
  obtain ⟨w, hw⟩ := gdr_exists_ulim xF _ hbd U
  refine ⟨w, fun p hp => ?_⟩
  apply gdr_weak_closed (U : Filter (Finset (H × H))) xF w p.1 p.2 hw
  have hat : ∀ᶠ F in (atTop : Filter (Finset (H × H))), ⟪xF F - p.1, xF F - p.2⟫_ℝ ≤ 0 := by
    filter_upwards [eventually_ge_atTop {p}] with F hF
    apply hxF F p
    apply Finset.mem_insert_of_mem
    exact Finset.mem_filter.2 ⟨hF (Finset.mem_singleton_self p), hp⟩
  exact Ultrafilter.of_le _ hat

lemma gdr_minty_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T) (c : ℝ) (hc : 0 < c) (w : H) :
    ∃ x y, y ∈ T x ∧ w = x + c • y := by
  set S : Set (H × H) := {p | c⁻¹ • (w - p.2) ∈ T p.1}
  have hmono : ∀ p ∈ S, ∀ q ∈ S, 0 ≤ ⟪p.1 - q.1, q.2 - p.2⟫_ℝ := by
    intro p hp q hq
    have h := hT.1 _ _ _ _ hp hq
    have e : q.2 - p.2 = c • (c⁻¹ • (w - p.2) - c⁻¹ • (w - q.2)) := by
      rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, one_smul]; abel
    rw [e, inner_smul_right]
    exact mul_nonneg hc.le h
  obtain ⟨x, hx⟩ := gdr_inf S hmono
  set y0 := c⁻¹ • (w - x)
  set T' : H → Set H := fun z => {y | y ∈ T z ∨ (z = x ∧ y = y0)}
  have hsub : ∀ z, T z ⊆ T' z := fun z y hy => Or.inl hy
  have key : ∀ z y, y ∈ T z → 0 ≤ ⟪z - x, y - y0⟫_ℝ := by
    intro z y hy
    have hp : (z, w - c • y) ∈ S := by
      show c⁻¹ • (w - (w - c • y)) ∈ T z
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]; exact hy
    have h := hx _ hp
    simp only at h
    have e : y - y0 = c⁻¹ • (x - (w - c • y)) := by
      simp only [y0]
      rw [smul_sub, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]; abel
    rw [e, inner_smul_right]
    have : ⟪z - x, x - (w - c • y)⟫_ℝ = -⟪x - z, x - (w - c • y)⟫_ℝ := by
      rw [← inner_neg_left, neg_sub]
    rw [this]
    exact mul_nonneg (inv_nonneg.2 hc.le) (by linarith)
  have hT'mono : IsMonotoneOp T' := by
    intro z1 z2 u1 u2 h1 h2
    rcases h1 with h1 | ⟨rfl, rfl⟩ <;> rcases h2 with h2 | ⟨rfl, rfl⟩
    · exact hT.1 _ _ _ _ h1 h2
    · exact key _ _ h1
    · have := key _ _ h2
      rw [← neg_sub z2, ← neg_sub u2, inner_neg_neg]; exact this
    · simp
  have hEq := hT.2 T' hT'mono hsub
  have hy0 : y0 ∈ T x := by
    have : y0 ∈ T' x := Or.inr ⟨rfl, rfl⟩
    rw [hEq] at this; exact this
  refine ⟨x, y0, hy0, ?_⟩
  simp only [y0]
  rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]; abel

lemma gdr_max_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMonotoneOp T) (c : ℝ) (hc : 0 < c) :
    IsMaximalMonotone T ↔ ∀ w, ∃ x y, y ∈ T x ∧ w = x + c • y := by
  constructor
  · intro h w; exact gdr_minty_core T h c hc w
  · intro hsurj
    refine ⟨hT, fun T' hT' hsub => ?_⟩
    funext z
    apply Set.Subset.antisymm _ (hsub z)
    intro u hu
    obtain ⟨x, y, hy, hw⟩ := hsurj (z + c • u)
    have hm := hT' z x u y hu (hsub x hy)
    have e : z - x = c • (y - u) := by
      rw [smul_sub]; linear_combination (norm := module) hw
    rw [e, inner_smul_left, RCLike.conj_to_real, ← neg_sub u y, inner_neg_left,
      real_inner_self_eq_norm_sq] at hm
    have hn : ‖u - y‖ ^ 2 ≤ 0 := by nlinarith
    have : u - y = 0 := by
      have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 (le_antisymm hn (sq_nonneg _))
      exact norm_eq_zero.1 this
    have huy : u = y := sub_eq_zero.1 this
    have hzx : z = x := by
      have : z - x = 0 := by rw [e, huy, sub_self, smul_zero]
      exact sub_eq_zero.1 this
    rw [huy, hzx]; exact hy

lemma gdr_mem_res {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (T : H → Set H) (w x : H) :
    x ∈ opResolvent c T w ↔ ∃ y ∈ T x, w = x + c • y := by
  simp only [opResolvent, opInv, opAdd, opId, opSmul, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl, b, ⟨y, hy, rfl⟩, h⟩; exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩; exact ⟨x, rfl, c • y, ⟨y, hy, rfl⟩, h⟩

theorem minty_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMonotoneOp T) :
    IsMaximalMonotone T ↔ imOp (opAdd opId T) = Set.univ := by
  rw [gdr_max_iff T hT 1 one_pos, Set.eq_univ_iff_forall]
  simp only [imOp, opAdd, opId, Set.mem_setOf_eq, Set.mem_singleton_iff, one_smul]
  constructor
  · intro h w
    obtain ⟨x, y, hy, hw⟩ := h w
    exact ⟨x, x, rfl, y, hy, hw⟩
  · intro h w
    obtain ⟨x, a, rfl, y, hy, hw⟩ := h w
    exact ⟨a, y, hy, hw⟩

lemma gdr_fne_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    IsMonotoneOp T ↔ IsFirmlyNonexpansiveOp (opResolvent c T) := by
  have expand : ∀ x x' y y' : H, ⟪(x' + c • y') - (x + c • y), x' - x⟫_ℝ
      = ‖x' - x‖ ^ 2 + c * ⟪x' - x, y' - y⟫_ℝ := by
    intro x x' y y'
    have : (x' + c • y') - (x + c • y) = (x' - x) + c • (y' - y) := by module
    rw [this, inner_add_left, real_inner_self_eq_norm_sq, inner_smul_left, RCLike.conj_to_real,
      real_inner_comm]
  constructor
  · intro hT w w' x x' hx hx'
    obtain ⟨y, hy, rfl⟩ := (gdr_mem_res c T w x).1 hx
    obtain ⟨y', hy', rfl⟩ := (gdr_mem_res c T w' x').1 hx'
    rw [expand]
    have := hT x' x y' y hy' hy
    nlinarith
  · intro hF x x' y y' hy hy'
    have h := hF (x' + c • y') (x + c • y) x' x ((gdr_mem_res c T _ _).2 ⟨y', hy', rfl⟩)
      ((gdr_mem_res c T _ _).2 ⟨y, hy, rfl⟩)
    rw [expand] at h
    have : 0 ≤ c * ⟪x - x', y - y'⟫_ℝ := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hc |> fun h' => by
      by_contra hneg; push_neg at hneg; nlinarith

theorem resolvent_fne_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    (IsMonotoneOp T ↔ IsFirmlyNonexpansiveOp (opResolvent c T)) ∧
    (IsMaximalMonotone T ↔
      IsFirmlyNonexpansiveOp (opResolvent c T) ∧ dom (opResolvent c T) = Set.univ) := by
  refine ⟨gdr_fne_iff c hc T, ?_⟩
  have hdom : dom (opResolvent c T) = Set.univ ↔ ∀ w, ∃ x y, y ∈ T x ∧ w = x + c • y := by
    rw [Set.eq_univ_iff_forall]
    simp only [dom, Set.mem_setOf_eq, Set.Nonempty, gdr_mem_res]
  constructor
  · intro hM
    exact ⟨(gdr_fne_iff c hc T).1 hM.1, hdom.2 ((gdr_max_iff T hM.1 c hc).1 hM)⟩
  · rintro ⟨hF, hD⟩
    have hT := (gdr_fne_iff c hc T).2 hF
    exact (gdr_max_iff T hT c hc).2 (hdom.1 hD)

lemma gdr_mem_M {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : H → Set H) (y u : H) :
    u ∈ opAdd (opInv K) (opSmul (-1) opId) y ↔ y ∈ K (u + y) := by
  simp only [opAdd, opInv, opSmul, opId, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, b, ⟨z, hz, hb⟩, hu⟩
    rw [hu, hb, hz]
    have : a + (-1:ℝ) • y + y = a := by module
    rw [this]; exact ha
  · intro h
    refine ⟨u + y, h, (-1:ℝ) • y, ⟨y, rfl, rfl⟩, ?_⟩
    module

theorem fne_inv_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : H → Set H) :
    (IsFirmlyNonexpansiveOp K ↔ IsMonotoneOp (opAdd (opInv K) (opSmul (-1) opId))) ∧
    (IsFirmlyNonexpansiveOp K ∧ dom K = Set.univ ↔
      IsMaximalMonotone (opAdd (opInv K) (opSmul (-1) opId))) := by
  set M := opAdd (opInv K) (opSmul (-1) opId)
  have p1 : IsFirmlyNonexpansiveOp K ↔ IsMonotoneOp M := by
    constructor
    · intro hF y y' u u' hu hu'
      rw [gdr_mem_M] at hu hu'
      have h := hF _ _ _ _ hu' hu
      have e : (u + y) - (u' + y') = (u - u') + (y - y') := by abel
      rw [e, inner_add_left, real_inner_self_eq_norm_sq] at h
      have e2 : ⟪u - u', y - y'⟫_ℝ = ⟪y - y', u - u'⟫_ℝ := real_inner_comm _ _
      rw [norm_sub_rev] at h
      linarith
    · intro hM x x' y y' hy hy'
      have h1 : (x - y) ∈ M y := (gdr_mem_M K y _).2 (by rw [sub_add_cancel]; exact hy)
      have h2 : (x' - y') ∈ M y' := (gdr_mem_M K y' _).2 (by rw [sub_add_cancel]; exact hy')
      have h := hM _ _ _ _ h2 h1
      rw [real_inner_comm] at h
      have e : x' - x = ((x' - y') - (x - y)) + (y' - y) := by abel
      rw [e, inner_add_left, real_inner_self_eq_norm_sq]
      linarith
  refine ⟨p1, ?_⟩
  have hdom : dom K = Set.univ ↔ ∀ w, ∃ x y, y ∈ M x ∧ w = x + (1:ℝ) • y := by
    rw [Set.eq_univ_iff_forall]
    simp only [dom, Set.Nonempty, one_smul]
    constructor
    · intro h w
      obtain ⟨y, hy⟩ := h w
      refine ⟨y, w - y, (gdr_mem_M K y _).2 (by rw [sub_add_cancel]; exact hy), by abel⟩
    · intro h w
      obtain ⟨x, y, hy, rfl⟩ := h w
      rw [gdr_mem_M] at hy
      exact ⟨x, by rw [add_comm]; exact hy⟩
  constructor
  · rintro ⟨hF, hD⟩
    have hM := p1.1 hF
    exact (gdr_max_iff M hM 1 one_pos).2 (hdom.1 hD)
  · intro hMax
    exact ⟨p1.2 hMax.1, hdom.2 ((gdr_max_iff M hMax.1 1 one_pos).1 hMax)⟩

lemma gdr_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) (hT : IsMonotoneOp T) :
    IsSingleValuedOp (opResolvent c T) := by
  intro w x x' hx hx'
  have h := (gdr_fne_iff c hc T).1 hT w w x x' hx hx'
  rw [sub_self, inner_zero_left] at h
  have : ‖x' - x‖ = 0 := by
    have := sq_nonneg ‖x' - x‖
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm h this)
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

theorem resolvent_sv_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    (IsMonotoneOp T → IsSingleValuedOp (opResolvent c T)) ∧
    (IsMaximalMonotone T → dom (opResolvent c T) = Set.univ) ∧
    (IsMaximalMonotone T → ∃! J : H → H, IsResolvent c T J) := by
  refine ⟨gdr_single c hc T, fun hM => ((resolvent_fne_core c hc T).2.1 hM).2, fun hM => ?_⟩
  have hex : ∀ w, ∃ x, x ∈ opResolvent c T w := by
    intro w
    obtain ⟨x, y, hy, hw⟩ := gdr_minty_core T hM c hc w
    exact ⟨x, (gdr_mem_res c T w x).2 ⟨y, hy, hw⟩⟩
  choose J hJ using hex
  have hres : ∀ J : H → H, IsResolvent c T J ↔ ∀ w, J w ∈ opResolvent c T w := by
    intro J
    constructor
    · intro h w
      refine (gdr_mem_res c T w (J w)).2 ⟨_, h w, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]; abel
    · intro h w
      obtain ⟨y, hy, hw⟩ := (gdr_mem_res c T w (J w)).1 (h w)
      have : c⁻¹ • (w - J w) = y := by
        rw [sub_eq_of_eq_add' hw, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [this]; exact hy
  refine ⟨J, (hres J).2 hJ, fun J' hJ' => ?_⟩
  funext w
  exact gdr_single c hc T hM.1 w _ _ (hJ w) ((hres J').1 hJ' w) |>.symm

theorem representation_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) (hT : IsMonotoneOp T) :
    (∀ z x y x' y' : H, y ∈ T x → y' ∈ T x' → z = x + c • y → z = x' + c • y' →
      x = x' ∧ y = y') ∧
    (IsMaximalMonotone T → ∀ z : H, ∃! p : H × H, p.2 ∈ T p.1 ∧ z = p.1 + c • p.2) := by
  have p1 : ∀ z x y x' y' : H, y ∈ T x → y' ∈ T x' → z = x + c • y → z = x' + c • y' →
      x = x' ∧ y = y' := by
    intro z x y x' y' hy hy' hz hz'
    have hxx := gdr_single c hc T hT z x x' ((gdr_mem_res c T z x).2 ⟨y, hy, hz⟩)
      ((gdr_mem_res c T z x').2 ⟨y', hy', hz'⟩)
    refine ⟨hxx, ?_⟩
    rw [hz, hxx] at hz'
    have := add_left_cancel hz'
    exact smul_right_injective H hc.ne' this
  refine ⟨p1, fun hM z => ?_⟩
  obtain ⟨x, y, hy, hz⟩ := gdr_minty_core T hM c hc z
  refine ⟨(x, y), ⟨hy, hz⟩, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := p1 z p.1 p.2 x y hp.1 hy hp.2 hz
  exact Prod.ext h1 h2

end DouglasRachfordPPA.GenDR

open DouglasRachfordPPA.GenDR


theorem bregman_existence_accepted_minty {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMonotoneOp T) :
    IsMaximalMonotone T ↔ imOp (opAdd opId T) = Set.univ := by
  exact minty_core T hT


end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Adjoining a related point to the exact original graph cannot extend a maximal operator. -/
theorem maximal_related_point (T : H → Set H) (hT : IsMaximalMonotone T) (z u : H)
    (hrel : ∀ v w : H, w ∈ T v → 0 ≤ inner ℝ (z-v) (u-w)) : u ∈ T z := by
  let U : H → Set H := fun x => T x ∪ {v | x=z ∧ v=u}
  have hU : IsMonotoneOp U := by
    intro x y v w hv hw
    rcases hv with hv | ⟨hx,hv⟩
    · rcases hw with hw | ⟨hy,hw⟩
      · exact hT.1 x y v w hv hw
      · rw [hy,hw]
        have he : inner ℝ (x-z) (v-u) = inner ℝ (z-x) (u-v) := by
          rw [← neg_sub z x,← neg_sub u v,inner_neg_left,inner_neg_right,neg_neg]
        rw [he]; exact hrel x v hv
    · rcases hw with hw | ⟨hy,hw⟩
      · rw [hx,hv]; exact hrel y w hw
      · rw [hx,hv,hy,hw]; simp
  have hEq : U=T := hT.2 U hU (fun x => Set.subset_union_left)
  have hu : u ∈ U z := Or.inr ⟨rfl,rfl⟩
  rwa [hEq] at hu

/-- Norm limits of graph points remain in the exact original maximal monotone graph. -/
theorem maximal_graph_limit (T : H → Set H) (hT : IsMaximalMonotone T)
    (x u : ℕ → H) (z v : H) (hx : Tendsto x atTop (𝓝 z)) (hu : Tendsto u atTop (𝓝 v))
    (hmem : ∀ k, u k ∈ T (x k)) : v ∈ T z := by
  apply maximal_related_point T hT z v
  intro y w hw
  have ht : Tendsto (fun k => inner ℝ (x k-y) (u k-w)) atTop (𝓝 (inner ℝ (z-y) (v-w))) :=
    (hx.sub_const y).inner (hu.sub_const w)
  exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht
    (Eventually.of_forall (fun k => hT.1 (x k) y (u k) w (hmem k) hw))
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Transport the original extended-real subgradient inequality only at verified finite points. -/
theorem subgradient_real_comparison (f : H → EReal) (hproper : IsProperFn f)
    {u v g : H} (hu : IsSubgradient f u g) (hv : f v ≠ ⊤) :
    (f u).toReal+inner ℝ g (v-u) ≤ (f v).toReal := by
  have heu := EReal.coe_toReal hu.1 (hproper.1 u)
  have hev := EReal.coe_toReal hv (hproper.1 v)
  have hg := hu.2 v
  rw [← heu,← hev,← EReal.coe_add] at hg
  exact EReal.coe_le_coe_iff.mp hg

theorem zero_subgradient_real_min (f : H → EReal) (hproper : IsProperFn f)
    {z v : H} (hz : IsSubgradient f z 0) (hv : f v ≠ ⊤) :
    (f z).toReal ≤ (f v).toReal := by
  simpa using subgradient_real_comparison f hproper hz hv

theorem zero_subgradient_of_min (f : H → EReal) {p : H} (hp : f p ≠ ⊤)
    (hmin : ∀ v : H, f p ≤ f v) : IsSubgradient f p 0 := by
  exact ⟨hp,fun v => by simpa using hmin v⟩

/-- Lower semicontinuity passes a verified objective-value limit to a boundary point. -/
theorem lsc_objective_limit (f : H → EReal) (hf : LowerSemicontinuous f)
    (x : ℕ → H) (p : H) (m : EReal) (hx : Tendsto x atTop (𝓝 p))
    (hm : Tendsto (fun k => f (x k)) atTop (𝓝 m)) : f p ≤ m := by
  by_contra hn
  have hmp : m < f p := lt_of_not_ge hn
  obtain ⟨a,hma,hap⟩ := exists_between hmp
  have hl : ∀ᶠ k in atTop, a < f (x k) := hx.eventually (hf p a hap)
  have hu : ∀ᶠ k in atTop, f (x k) < a := hm.eventually (Iio_mem_nhds hma)
  obtain ⟨k,hk⟩ := (hl.and hu).exists
  exact lt_asymm hk.1 hk.2
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- First-order support at a point in the original open zone, including boundary test points. -/
theorem gradient_support (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {y z : H} (hy : y ∈ S) (hz : z ∈ closure S) :
    inner ℝ (gradient h y) (z-y) ≤ h z-h y := by
  have hd : DifferentiableAt ℝ h y :=
    ((hh.contDiffOn.differentiableOn (by simp)) y hy).differentiableAt (hh.isOpen.mem_nhds hy)
  let l : ℝ →ᵃ[ℝ] H := AffineMap.lineMap y z
  have hcv := hh.strictConvexOn.convexOn.comp_affineMap l
  have h0 : (0 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using subset_closure hy
  have h1 : (1 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using hz
  have hder : HasDerivAt (h ∘ l) (fderiv ℝ h y (z-y)) 0 := by
    apply hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := (0 : ℝ)))
    simp [l]
  have hs := hcv.le_slope_of_hasDerivAt h0 h1 (by norm_num) hder
  simpa [l,slope,inner_gradient_left] using hs

theorem bregman_nonneg (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {x y : H} (hx : x ∈ closure S) (hy : y ∈ S) : 0 ≤ bregmanD h x y := by
  have hs := gradient_support S h hh hy hx
  dsimp [bregmanD]; linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
section

open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace BregmanPPA.Existence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A trimonotone (3-cyclically monotone) operator, in the sense of Brézis–Haraux [5]: for all
`(x₀, y₀), (x₁, y₁), (x₂, y₂)` in the graph of `R`,
`⟪x₁ − x₀, y₀⟫ + ⟪x₂ − x₁, y₁⟫ + ⟪x₀ − x₂, y₂⟫ ≤ 0`. -/
def IsTrimonotone (R : H → Set H) : Prop :=
  ∀ x₀ x₁ x₂ y₀ y₁ y₂ : H, y₀ ∈ R x₀ → y₁ ∈ R x₁ → y₂ ∈ R x₂ →
    inner ℝ (x₁ - x₀) y₀ + inner ℝ (x₂ - x₁) y₁ + inner ℝ (x₀ - x₂) y₂ ≤ 0

/-- Definition 2 (p. 208): a monotone operator `R` has the L-property if, for all `u ∈ dom R`
and `v ∈ im R`, `inf {⟪x − u, y − v⟫ | x ∈ dom R, y ∈ R x} > −∞`. -/
def HasLProperty (R : H → Set H) : Prop :=
  IsMonotoneOp R ∧ ∀ u ∈ dom R, ∀ v ∈ imOp R,
    BddBelow {t : ℝ | ∃ x y, y ∈ R x ∧ t = inner ℝ (x - u) (y - v)}

end BregmanPPA.Existence

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open scoped Pointwise
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- A lower bound on graph pairings gives norm approximation by graph outputs. -/
theorem range_closure_of_pairing_bound (C : H → Set H) (hC : IsMaximalMonotone C)
    (r u : H) (M : ℝ)
    (hb : ∀ x y : H, y ∈ C x → M ≤ inner ℝ (x-u) (y-r)) :
    r ∈ closure (imOp C) := by
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  let K : ℝ := ‖u‖^2 + 2*|M| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let t : ℝ := min 1 (δ^2/(2*K))
  have ht : 0 < t := lt_min one_pos (div_pos (sq_pos_of_pos hδ) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have hsmall : t*K ≤ δ^2/2 := by
    have h := min_le_right (1 : ℝ) (δ^2/(2*K))
    change t ≤ δ^2/(2*K) at h
    have := (le_div_iff₀ (show 0 < 2*K by positivity)).mp h
    linarith
  obtain ⟨x,y,hy,he⟩ := gdr_minty_core C hC t⁻¹ (inv_pos.mpr ht) (t⁻¹ • r)
  have hr : r = t • x + y := by
    have := congrArg (fun z : H => t • z) he
    simpa only [smul_add,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using this
  have hv : r-y = t • x := by rw [hr]; abel
  have hpair := hb x y hy
  have hh : ‖t • x‖^2 ≤ t * inner ℝ u (t • x) - t*M := by
    rw [show y-r = -(t • x) by rw [← hv]; abel] at hpair
    simp only [inner_neg_right,inner_smul_right,inner_sub_left,
      real_inner_self_eq_norm_sq] at hpair
    have hh := mul_le_mul_of_nonneg_left hpair ht.le
    rw [norm_smul,Real.norm_of_nonneg ht.le]
    simp only [inner_smul_right]
    nlinarith
  have hcs : inner ℝ u (t • x) ≤ ‖u‖*‖t • x‖ := real_inner_le_norm _ _
  have hM : -M ≤ |M| := neg_le_abs M
  have hq : ‖t • x‖^2 ≤ t^2*‖u‖^2 + 2*t*|M| := by
    nlinarith [sq_nonneg (‖t • x‖-t*‖u‖)]
  have hq2 : ‖t • x‖^2 < δ^2 := by
    have hpow : t^2 ≤ t := by nlinarith
    have hu := mul_le_mul_of_nonneg_right hpow (sq_nonneg ‖u‖)
    dsimp [K] at hsmall
    nlinarith
  refine ⟨y, ⟨x,hy⟩, ?_⟩
  rw [dist_eq_norm,hv]
  nlinarith [norm_nonneg (t • x)]

/-- The original L-property supplies the pairing bound for every sum of range points. -/
theorem sum_ranges_subset_closure (A B : H → Set H)
    (hA : IsMonotoneOp A) (ha : dom A ⊆ dom B)
    (hC : IsMaximalMonotone (opAdd A B))
    (hB : BregmanPPA.Existence.HasLProperty B) :
    imOp A + imOp B ⊆ closure (imOp (opAdd A B)) := by
  intro r hr
  obtain ⟨a,ha',b,hb',rfl⟩ := Set.mem_add.mp hr
  obtain ⟨u,hu⟩ := ha'
  have huB : u ∈ dom B := ha ⟨a,hu⟩
  obtain ⟨M,hM⟩ := hB.2 u huB b hb'
  apply range_closure_of_pairing_bound (opAdd A B) hC (a+b) u M
  intro x y hy
  obtain ⟨a',ha',b',hb',rfl⟩ := hy
  have hm := hA x u a' a ha' hu
  have hl := hM (show inner ℝ (x-u) (b'-b) ∈
      {t : ℝ | ∃ x y, y ∈ B x ∧ t = inner ℝ (x-u) (y-b)} from
        ⟨x,b',hb',rfl⟩)
  have he : inner ℝ (x-u) (a'+b'-(a+b)) =
      inner ℝ (x-u) (a'-a) + inner ℝ (x-u) (b'-b) := by
    rw [show a'+b'-(a+b) = (a'-a)+(b'-b) by abel,inner_add_right]
  rw [he]; linarith

/-- The full closure equality from the original range milestone. -/
theorem range_closure_equality (A B : H → Set H)
    (hA : IsMonotoneOp A) (ha : dom A ⊆ dom B)
    (hC : IsMaximalMonotone (opAdd A B))
    (hB : BregmanPPA.Existence.HasLProperty B) :
    closure (imOp (opAdd A B)) = closure (imOp A + imOp B) := by
  apply Set.Subset.antisymm
  · apply closure_mono
    intro y hy
    obtain ⟨x,a,ha',b,hb',rfl⟩ := hy
    exact Set.mem_add.mpr ⟨a,⟨x,ha'⟩,b,⟨x,hb'⟩,rfl⟩
  · exact closure_minimal (sum_ranges_subset_closure A B hA ha hC hB) isClosed_closure
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR Filter Topology Finset
open scoped Pointwise
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem norm_le_basis_pairings {I : Type*} [Fintype I]
    (e : OrthonormalBasis I ℝ H) (x : H) :
    ‖x‖ ≤ ∑ i, |inner ℝ x (e i)| := by
  classical
  calc
    ‖x‖ = ‖∑ i, inner ℝ (e i) x • e i‖ := congrArg norm (e.sum_repr' x).symm
    _ ≤ ∑ i, ‖inner ℝ (e i) x • e i‖ := norm_sum_le _ _
    _ = ∑ i, |inner ℝ x (e i)| := by
      apply sum_congr rfl; intro i _
      rw [norm_smul,Real.norm_eq_abs,e.norm_eq_one,mul_one,real_inner_comm]

theorem regularized_direction_bound (C : H → Set H) (r u x y e : H)
    (s t M : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (he : ‖e‖ = 1)
    (hy : y ∈ C x) (hr : r = t • x+y)
    (hb : ∀ z w : H, w ∈ C z → M ≤ inner ℝ (z-u) (w-(r+s • e))) :
    s*inner ℝ x e ≤ s*‖u‖ + t*‖u‖*‖x‖ + |M| := by
  have h := hb x y hy
  have hvec : y-(r+s • e) = -(t • x)-s • e := by rw [hr]; module
  rw [hvec,inner_sub_right,inner_neg_right,inner_smul_right,inner_smul_right,
    inner_sub_left,inner_sub_left,real_inner_self_eq_norm_sq] at h
  have hu := real_inner_le_norm u x
  have hue := real_inner_le_norm u e
  rw [he,mul_one] at hue
  have hn := mul_nonneg ht (sq_nonneg ‖x‖)
  have htU := mul_le_mul_of_nonneg_left hu ht
  have hsU := mul_le_mul_of_nonneg_left hue hs
  nlinarith [neg_le_abs M]

theorem regularized_basis_bound {I : Type*} [Fintype I]
    (e : OrthonormalBasis I ℝ H) (C : H → Set H) (r x y : H)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hy : y ∈ C x) (hr : r=t • x+y)
    (uP uN : I → H) (mP mN : I → ℝ)
    (hP : ∀ i z w, w ∈ C z → mP i ≤ inner ℝ (z-uP i) (w-(r+s • e i)))
    (hN : ∀ i z w, w ∈ C z → mN i ≤ inner ℝ (z-uN i) (w-(r-s • e i))) :
    s*‖x‖ ≤ (∑ i, (s*(‖uP i‖+‖uN i‖)+|mP i|+|mN i|)) +
      t*(∑ i, (‖uP i‖+‖uN i‖))*‖x‖ := by
  classical
  have hb (i : I) : s*|inner ℝ x (e i)| ≤
      s*(‖uP i‖+‖uN i‖)+|mP i|+|mN i|+t*(‖uP i‖+‖uN i‖)*‖x‖ := by
    have hp := regularized_direction_bound C r (uP i) x y (e i) s t (mP i)
      hs ht (e.norm_eq_one i) hy hr (hP i)
    have hn := regularized_direction_bound C r (uN i) x y (-e i) s t (mN i)
      hs ht (by rw [norm_neg,e.norm_eq_one]) hy hr (by simpa only [smul_neg,sub_eq_add_neg] using hN i)
    rw [inner_neg_right] at hn
    have hnP : 0 ≤ s*‖uP i‖+t*‖uP i‖*‖x‖+|mP i| := by positivity
    have hnN : 0 ≤ s*‖uN i‖+t*‖uN i‖*‖x‖+|mN i| := by positivity
    have habs : s*|inner ℝ x (e i)| = |s*inner ℝ x (e i)| := by
      rw [abs_mul,abs_of_nonneg hs]
    rw [habs]
    apply abs_le.mpr
    constructor <;> nlinarith
  calc
    s*‖x‖ ≤ s*(∑ i, |inner ℝ x (e i)|) :=
      mul_le_mul_of_nonneg_left (norm_le_basis_pairings e x) hs
    _ = ∑ i, s*|inner ℝ x (e i)| := mul_sum _ _ _
    _ ≤ ∑ i, (s*(‖uP i‖+‖uN i‖)+|mP i|+|mN i|+t*(‖uP i‖+‖uN i‖)*‖x‖) := sum_le_sum fun i _ => hb i
    _ = _ := by simp only [sum_add_distrib,sum_mul,mul_sum,mul_add,add_mul]
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR Filter Topology Finset
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem mem_range_of_ball_pairing_bounds (C : H → Set H) (hC : IsMaximalMonotone C)
    (r : H) (δ : ℝ) (hδ : 0 < δ)
    (hb : ∀ v ∈ Metric.ball r δ, ∃ u : H, ∃ M : ℝ,
      ∀ x y : H, y ∈ C x → M ≤ inner ℝ (x-u) (y-v)) : r ∈ imOp C := by
  classical
  let e := stdOrthonormalBasis ℝ H
  let s : ℝ := δ/2
  have hs : 0 < s := by dsimp [s]; positivity
  have hp (i : Fin (Module.finrank ℝ H)) : r+s • e i ∈ Metric.ball r δ := by
    rw [Metric.mem_ball,dist_eq_norm,show r+s • e i-r=s • e i by abel,
      norm_smul,Real.norm_of_nonneg hs.le,e.norm_eq_one,mul_one]
    dsimp [s]; linarith
  have hn (i : Fin (Module.finrank ℝ H)) : r-s • e i ∈ Metric.ball r δ := by
    rw [Metric.mem_ball,dist_eq_norm,show r-s • e i-r=-(s • e i) by abel,
      norm_neg,norm_smul,Real.norm_of_nonneg hs.le,e.norm_eq_one,mul_one]
    dsimp [s]; linarith
  choose uP mP hP using fun i => hb (r+s • e i) (hp i)
  choose uN mN hN using fun i => hb (r-s • e i) (hn i)
  let U : ℝ := ∑ i, (‖uP i‖+‖uN i‖)
  let K : ℝ := ∑ i, (s*(‖uP i‖+‖uN i‖)+|mP i|+|mN i|)
  have hU : 0 ≤ U := sum_nonneg fun i _ => by positivity
  have hK : 0 ≤ K := sum_nonneg fun i _ => by positivity
  let a : ℝ := s/(2*(U+1))
  have ha : 0 < a := div_pos hs (by positivity)
  have haU : a*U ≤ s/2 := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2*(U+1) by positivity)).mpr
    nlinarith
  let t : ℕ → ℝ := fun n => a/(n+1 : ℝ)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hta (n : ℕ) : t n ≤ a := by
    dsimp [t]; apply (div_le_iff₀ (by positivity : 0 < (n+1 : ℝ))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htu (n : ℕ) : t n*U ≤ s/2 :=
    (mul_le_mul_of_nonneg_right (hta n) hU).trans haU
  have htz : Tendsto t atTop (𝓝 0) := by
    simpa [t,div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => a*(1/(n+1 : ℝ))) atTop (𝓝 (a*0)))
  choose x y hym hem using fun n =>
    gdr_minty_core C hC (t n)⁻¹ (inv_pos.mpr (ht n)) ((t n)⁻¹ • r)
  have hr (n : ℕ) : r=t n • x n+y n := by
    have hh := congrArg (fun z : H => t n • z) (hem n)
    simpa only [smul_add,smul_smul,mul_inv_cancel₀ (ht n).ne',one_smul] using hh
  have hxb (n : ℕ) : ‖x n‖ ≤ 2*K/s := by
    have h := regularized_basis_bound e C r (x n) (y n) s (t n) hs.le (ht n).le
      (hym n) (hr n) uP uN mP mN hP hN
    change s*‖x n‖ ≤ K+t n*U*‖x n‖ at h
    have hu := mul_le_mul_of_nonneg_right (htu n) (norm_nonneg (x n))
    apply (le_div_iff₀ hs).mpr
    nlinarith
  have hbounded : Bornology.IsBounded (Set.range x) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨2*K/s,fun z hz => by obtain ⟨n,rfl⟩ := hz; exact hxb n⟩
  obtain ⟨p,_,φ,hφ,hlim⟩ := tendsto_subseq_of_bounded hbounded (fun n => Set.mem_range_self n)
  have hprod : Tendsto (fun n => t (φ n) • x (φ n)) atTop (𝓝 (0 : H)) := by
    simpa using (htz.comp hφ.tendsto_atTop).smul hlim
  have hy : Tendsto (fun n => y (φ n)) atTop (𝓝 r) := by
    have hh : y = fun n => r-t n • x n := by funext n; rw [hr n]; abel
    rw [hh]
    simpa using tendsto_const_nhds.sub hprod
  exact ⟨p,BregmanPPACodex.maximal_graph_limit C hC (x ∘ φ) (y ∘ φ) p r
    hlim hy (fun n => hym (φ n))⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open scoped Pointwise
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem sum_range_pairing_bound (A B : H → Set H)
    (hA : IsMonotoneOp A) (ha : dom A ⊆ dom B)
    (hB : BregmanPPA.Existence.HasLProperty B) (r : H) (hr : r ∈ imOp A+imOp B) :
    ∃ u : H, ∃ M : ℝ, ∀ x y : H, y ∈ opAdd A B x → M ≤ inner ℝ (x-u) (y-r) := by
  obtain ⟨a,ha',b,hb',rfl⟩ := Set.mem_add.mp hr
  obtain ⟨u,hu⟩ := ha'
  obtain ⟨M,hM⟩ := hB.2 u (ha ⟨a,hu⟩) b hb'
  refine ⟨u,M,?_⟩
  intro x y hy
  obtain ⟨a',ha',b',hb',rfl⟩ := hy
  have hm := hA x u a' a ha' hu
  have hl := hM (show inner ℝ (x-u) (b'-b) ∈
      {t : ℝ | ∃ x y, y ∈ B x ∧ t = inner ℝ (x-u) (y-b)} from ⟨x,b',hb',rfl⟩)
  rw [show a'+b'-(a+b) = (a'-a)+(b'-b) by abel,inner_add_right]
  linarith

theorem range_interior_equality (A B : H → Set H)
    (hA : IsMonotoneOp A) (ha : dom A ⊆ dom B)
    (hC : IsMaximalMonotone (opAdd A B))
    (hB : BregmanPPA.Existence.HasLProperty B) :
    interior (imOp (opAdd A B)) = interior (imOp A+imOp B) := by
  have hsum : imOp (opAdd A B) ⊆ imOp A+imOp B := by
    intro y hy
    obtain ⟨x,a,ha',b,hb',rfl⟩ := hy
    exact Set.mem_add.mpr ⟨a,⟨x,ha'⟩,b,⟨x,hb'⟩,rfl⟩
  have hi : interior (imOp A+imOp B) ⊆ imOp (opAdd A B) := by
    intro r hr
    obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hr)
    exact mem_range_of_ball_pairing_bounds (opAdd A B) hC r δ hδ
      (fun v hv => sum_range_pairing_bound A B hA ha hB v (hball hv))
  exact Set.Subset.antisymm (interior_mono hsum) (interior_maximal hi isOpen_interior)
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR InertialFB.IFB
namespace BregmanExistenceCodex
open BregmanPPA.Existence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem trimonotone_monotone (R : H → Set H) (hR : IsTrimonotone R) :
    IsMonotoneOp R := by
  intro x z y w hy hw
  have hc := hR x z x y w y hy hw hy
  simp only [sub_self, inner_zero_left, add_zero] at hc
  simp only [inner_sub_left] at hc
  simp only [inner_sub_left, inner_sub_right]
  linarith

theorem trimonotone_lproperty (R : H → Set H) (hR : IsTrimonotone R) :
    HasLProperty R := by
  refine ⟨trimonotone_monotone R hR, ?_⟩
  intro u hu v hv
  obtain ⟨a, ha⟩ := hu
  obtain ⟨q, hq⟩ := hv
  refine ⟨inner ℝ (q-u) a + inner ℝ (u-q) v, ?_⟩
  intro t ht
  obtain ⟨x,y,hy,rfl⟩ := ht
  have hc := hR x u q y a v hy ha hq
  simp only [inner_sub_left, inner_sub_right] at hc ⊢
  linarith

theorem subdiff_trimonotone (f : H → EReal) (hp : IsProperFn f) :
    IsTrimonotone (BregmanPPA.Convergence.subdiffOp f) := by
  intro x₀ x₁ x₂ y₀ y₁ y₂ h₀ h₁ h₂
  have h01 := BregmanPPACodex.subgradient_real_comparison f hp h₀ h₁.1
  have h12 := BregmanPPACodex.subgradient_real_comparison f hp h₁ h₂.1
  have h20 := BregmanPPACodex.subgradient_real_comparison f hp h₂ h₀.1
  rw [real_inner_comm] at h01 h12 h20
  linarith
end BregmanExistenceCodex

end

section
set_option autoImplicit false
namespace BregmanExistenceCodex
open BregmanPPA.Existence BregmanPPA.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem gradient_trimonotone (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h) :
    IsTrimonotone (gradOp S h) := by
  intro x₀ x₁ x₂ y₀ y₁ y₂ h₀ h₁ h₂
  obtain ⟨hx₀,rfl⟩ := h₀
  obtain ⟨hx₁,rfl⟩ := h₁
  obtain ⟨hx₂,rfl⟩ := h₂
  have h01 := BregmanPPACodex.gradient_support S h hh hx₀ (subset_closure hx₁)
  have h12 := BregmanPPACodex.gradient_support S h hh hx₁ (subset_closure hx₂)
  have h20 := BregmanPPACodex.gradient_support S h hh hx₂ (subset_closure hx₀)
  rw [real_inner_comm] at h01 h12 h20
  linarith

theorem gradient_lproperty (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h) :
    HasLProperty (gradOp S h) :=
  trimonotone_lproperty _ (gradient_trimonotone S h hh)
end BregmanExistenceCodex

end


end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- The inverse of A+dI is a continuous monotone field, directly from the original Minty graph. -/
theorem inverse_field_exists (A : H → Set H) (hA : IsMaximalMonotone A)
    (d : ℝ) (hd : 0 < d) :
    ∃ J : H → H, Continuous J ∧ (∀ v, v-d • J v ∈ A (J v)) ∧
      (∀ v w, d*‖J v-J w‖^2 ≤ inner ℝ (J v-J w) (v-w)) := by
  classical
  choose J a ha he using fun v : H => gdr_minty_core A hA d⁻¹ (inv_pos.mpr hd) (d⁻¹ • v)
  have hmem (v : H) : v-d • J v ∈ A (J v) := by
    have hv := congrArg (fun z : H => d • z) (he v)
    simp only [smul_add,smul_smul,mul_inv_cancel₀ hd.ne',one_smul] at hv
    have heq : v-d • J v=a v := by
      calc
        v-d • J v=(d • J v+a v)-d • J v := congrArg (fun z => z-d • J v) hv
        _=a v := by abel
    rw [heq]; exact ha v
  have hstrong (v w : H) : d*‖J v-J w‖^2 ≤ inner ℝ (J v-J w) (v-w) := by
    have h := hA.1 (J v) (J w) (v-d • J v) (w-d • J w) (hmem v) (hmem w)
    have hv : (v-d • J v)-(w-d • J w)=(v-w)-d • (J v-J w) := by module
    rw [hv,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq] at h
    linarith
  have hlip : LipschitzWith (Real.toNNReal d⁻¹) J := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ (inv_nonneg.mpr hd.le)]
    have h := hstrong v w
    have hc := real_inner_le_norm (J v-J w) (v-w)
    by_cases hn : ‖J v-J w‖=0
    · rw [hn]; positivity
    have hp : 0 < ‖J v-J w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hb : d*‖J v-J w‖ ≤ ‖v-w‖ := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul] using hh
  exact ⟨J,hlip.continuous,hmem,hstrong⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem inverse_pairing_lower (B : H → Set H) (hB : IsMonotoneOp B)
    (J : H → H) (d R δ K : ℝ) (hd : 0 ≤ d) (hR : 0 ≤ R) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hmem : ∀ v, v-d • J v ∈ B (J v)) (hbound : ∀ x y, y ∈ B x → ‖x‖ ≤ R)
    (hlocal : ∀ x ∈ Metric.ball (0 : H) δ, ∃ b ∈ B x, ‖b‖ ≤ K)
    (v : H) (hv : 0 < ‖v‖) :
    (δ/2)*‖v‖-d*(δ/2)*R-(R+δ/2)*K ≤ inner ℝ (J v) v := by
  let z : H := ((δ/2)/‖v‖) • v
  have hz : ‖z‖=δ/2 := by
    rw [norm_smul,Real.norm_of_nonneg (div_nonneg (by positivity) hv.le),div_mul_cancel₀ (δ / 2) hv.ne']
  have hzB : z ∈ Metric.ball (0 : H) δ := by
    rw [Metric.mem_ball,dist_zero_right,hz]; linarith
  obtain ⟨b,hb,hbK⟩ := hlocal z hzB
  have hJ := hbound (J v) (v-d • J v) (hmem v)
  have hp := hB (J v) z (v-d • J v) b (hmem v) hb
  have hzv : inner ℝ z v=(δ/2)*‖v‖ := by
    dsimp [z]; rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp [hv.ne']
  have he : inner ℝ (J v-z) ((v-d • J v)-b) =
      inner ℝ (J v) v-inner ℝ z v-d*‖J v‖^2+d*inner ℝ z (J v)-
      inner ℝ (J v) b+inner ℝ z b := by
    simp only [inner_sub_left,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq]
    ring
  rw [he,hzv] at hp
  have h1 := real_inner_le_norm z (J v)
  have h2 := real_inner_le_norm (-J v) b
  have h3 := real_inner_le_norm z b
  rw [hz] at h1 h3
  rw [inner_neg_left,norm_neg] at h2
  have hd1 := mul_le_mul_of_nonneg_left h1 hd
  have hdR := mul_le_mul_of_nonneg_left hJ (show 0 ≤ d*(δ/2) by positivity)
  have hRK := mul_le_mul hJ hbK (norm_nonneg b) hR
  have hδK := mul_le_mul_of_nonneg_left hbK (show 0 ≤ δ/2 by positivity)
  nlinarith [mul_nonneg hd (sq_nonneg ‖J v‖)]
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace MartinetVICodex

/-- A finite bilinear minimax criterion, applied below to original monotone operators.
The Sion interface follows the repository's Hart-Schmeidler minimax pattern. -/
theorem finite_minimax_criterion {I : Type*} [Fintype I] [Nonempty I]
    (A : I → I → ℝ)
    (hA : ∀ p ∈ stdSimplex ℝ I, 0 ≤ ∑ i, ∑ j, p i*p j*A i j) :
    ∃ q ∈ stdSimplex ℝ I, ∀ p ∈ stdSimplex ℝ I,
      0 ≤ ∑ i, ∑ j, p i*q j*A i j := by
  classical
  let f : (I → ℝ) → (I → ℝ) → ℝ := fun p q => ∑ i, ∑ j, p i*q j*A i j
  have hc1 (q : I → ℝ) : Continuous (fun p => f p q) := by dsimp [f]; fun_prop
  have hc2 (p : I → ℝ) : Continuous (fun q => f p q) := by dsimp [f]; fun_prop
  have hl1 (q p p' : I → ℝ) (a b : ℝ) :
      f (a • p+b • p') q = a*f p q+b*f p' q := by
    simp only [f,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  have hl2 (p q q' : I → ℝ) (a b : ℝ) :
      f p (a • q+b • q') = a*f p q+b*f p q' := by
    simp only [f,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  have hconv (q : I → ℝ) : ConvexOn ℝ (stdSimplex ℝ I) (fun p => f p q) := by
    refine ⟨convex_stdSimplex ℝ I, ?_⟩
    intro p _ p' _ a b _ _ _
    change f (a • p+b • p') q ≤ a*f p q+b*f p' q
    rw [hl1]
  have hconc (p : I → ℝ) : ConcaveOn ℝ (stdSimplex ℝ I) (fun q => f p q) := by
    refine ⟨convex_stdSimplex ℝ I, ?_⟩
    intro q _ q' _ a b _ _ _
    change a*f p q+b*f p q' ≤ f p (a • q+b • q')
    rw [hl2]
  have hne : (stdSimplex ℝ I).Nonempty :=
    ⟨Pi.single (Classical.arbitrary I) 1,single_mem_stdSimplex ℝ _⟩
  obtain ⟨p,hp,q,hq,hs⟩ := Sion.exists_isSaddlePointOn (X := stdSimplex ℝ I)
    (Y := stdSimplex ℝ I) (f := f) hne (convex_stdSimplex ℝ I)
    (isCompact_stdSimplex ℝ I)
    (fun q _ => (hc1 q).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun q _ => (hconv q).quasiconvexOn)
    (convex_stdSimplex ℝ I) hne (isCompact_stdSimplex ℝ I)
    (fun p _ => (hc2 p).upperSemicontinuous.upperSemicontinuousOn _)
    (fun p _ => (hconc p).quasiconcaveOn)
  exact ⟨q,hq,fun p' hp' => (hA p hp).trans (hs p' hp' p hp)⟩

/-- Pairwise nonnegative symmetric sums supply the finite minimax premise. -/
theorem matrix_simplex_nonneg {I : Type*} [Fintype I] (A : I → I → ℝ)
    (hA : ∀ i j, 0 ≤ A i j+A j i) (p : I → ℝ) (hp : p ∈ stdSimplex ℝ I) :
    0 ≤ ∑ i, ∑ j, p i*p j*A i j := by
  classical
  have ht : (∑ i, ∑ j, p i*p j*A j i) = ∑ i, ∑ j, p i*p j*A i j := by
    rw [sum_comm]; apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _; ring
  have hn : 0 ≤ ∑ i, ∑ j, p i*p j*(A i j+A j i) :=
    sum_nonneg fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hp.1 i) (hp.1 j)) (hA i j)
  have he : (∑ i, ∑ j, p i*p j*(A i j+A j i)) =
      (∑ i, ∑ j, p i*p j*A i j)+(∑ i, ∑ j, p i*p j*A j i) := by
    simp only [mul_add,sum_add_distrib]
  rw [he,ht] at hn; linarith
end MartinetVICodex

end

section
set_option autoImplicit false
open Set Filter Topology Finset
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem finite_primal_minty {I : Type*} [Fintype I] [Nonempty I]
    (F : H → H) (C : Set H) (hC : Convex ℝ C)
    (hm : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (x-y) (F x-F y))
    (y : I → H) (hy : ∀ i, y i ∈ C) :
    ∃ u ∈ C, ∀ i, 0 ≤ inner ℝ (F (y i)) (y i-u) := by
  classical
  let A : I → I → ℝ := fun i j => inner ℝ (F (y i)) (y i-y j)
  have hA (i j : I) : 0 ≤ A i j+A j i := by
    have h := hm (y i) (hy i) (y j) (hy j)
    have he : inner ℝ (F (y j)) (y j-y i) = -inner ℝ (F (y j)) (y i-y j) := by
      rw [← neg_sub (y i) (y j),inner_neg_right]
    dsimp [A]; rw [he]
    rw [real_inner_comm,inner_sub_left] at h
    simpa only [sub_eq_add_neg] using h
  obtain ⟨q,hq,hqs⟩ := MartinetVICodex.finite_minimax_criterion A
    (fun p hp => MartinetVICodex.matrix_simplex_nonneg A hA p hp)
  let u := ∑ j, q j • y j
  have hu : u ∈ C := hC.sum_mem (fun i _ => hq.1 i) hq.2 (fun i _ => hy i)
  refine ⟨u,hu,fun i => ?_⟩
  have hi : 0 ≤ ∑ j, q j*A i j := by
    simpa [Pi.single_apply] using hqs (Pi.single i 1) (single_mem_stdSimplex ℝ i)
  have he : inner ℝ (F (y i)) (y i-u) = ∑ j, q j*A i j := by
    simp only [u,A,inner_sub_right,inner_sum,inner_smul_right,mul_sub,sum_sub_distrib,
      ← sum_mul,hq.2,one_mul]
  rw [he]; exact hi

theorem compact_primal_vi (F : H → H) (C : Set H) (hc : IsCompact C)
    (hcv : Convex ℝ C) (hne : C.Nonempty) (hf : ContinuousOn F C)
    (hm : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (x-y) (F x-F y)) :
    ∃ u ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (F u) (y-u) := by
  classical
  let K : C → Set H := fun y => {w | 0 ≤ inner ℝ (F y.val) (y.val-w)}
  have hK (y : C) : IsClosed (K y) := by
    apply isClosed_le continuous_const
    fun_prop
  have hfinite (s : Finset C) : (C ∩ ⋂ y ∈ s, K y).Nonempty := by
    by_cases hs : s.Nonempty
    · let : Nonempty ↑s := ⟨⟨hs.choose,hs.choose_spec⟩⟩
      obtain ⟨u,hu,hus⟩ := finite_primal_minty F C hcv hm (fun i : s => i.val.val)
        (fun i => i.val.property)
      refine ⟨u,hu,?_⟩
      simp only [mem_iInter]
      intro y hy
      exact hus ⟨y,hy⟩
    · obtain ⟨u,hu⟩ := hne
      have hs0 : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp only [hs0,Finset.notMem_empty,iInter_of_empty,iInter_univ,inter_univ]
      exact ⟨u,hu⟩
  obtain ⟨u,hu,hKu⟩ := hc.inter_iInter_nonempty K hK hfinite
  have hminty (y : H) (hy : y ∈ C) : 0 ≤ inner ℝ (F y) (y-u) :=
    mem_iInter.mp hKu ⟨y,hy⟩
  refine ⟨u,hu,?_⟩
  intro y hy
  let a : ℕ → ℝ := fun n => 1/(n+1 : ℝ)
  have ha (n : ℕ) : 0 < a n ∧ a n ≤ 1 := by
    dsimp [a]; constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n+1 : ℝ))).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  let z : ℕ → H := fun n => (1-a n) • u+a n • y
  have hz (n : ℕ) : z n ∈ C := hcv hu hy (by linarith [(ha n).2]) (ha n).1.le (by ring)
  have hlim : Tendsto z atTop (𝓝 u) := by
    have haz : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [z] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub haz).smul_const u |>.add (haz.smul_const y)
  have hzlim : Tendsto z atTop (𝓝[C] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall hz⟩
  have hFlim := (hf u hu).tendsto.comp hzlim
  have hp (n : ℕ) : 0 ≤ inner ℝ (F (z n)) (y-u) := by
    have h := hminty (z n) (hz n)
    have he : z n-u=a n • (y-u) := by dsimp [z]; module
    rw [he,inner_smul_right] at h
    exact nonneg_of_mul_nonneg_right h (ha n).1
  exact (isClosed_Ici : IsClosed (Ici (0 : ℝ))).mem_of_tendsto
    (hFlim.inner tendsto_const_nhds) (Eventually.of_forall hp)
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR Filter Topology
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- Normal vectors to the closed ball, represented as a local helper operator. -/
def normal_ball (R : ℝ) : H → Set H := fun x =>
  {n | x ∈ Metric.closedBall (0 : H) R ∧ ∀ z ∈ Metric.closedBall (0 : H) R,
    inner ℝ (z-x) n ≤ 0}

theorem normal_ball_monotone (R : ℝ) : IsMonotoneOp (normal_ball (H := H) R) := by
  intro x y u v hu hv
  have h1 := hu.2 y hv.1
  have h2 := hv.2 x hu.1
  rw [← neg_sub x y,inner_neg_left] at h1
  rw [inner_sub_right]
  linarith

theorem normal_ball_zero_mem (R : ℝ) {x : H} (hx : x ∈ Metric.closedBall (0 : H) R) :
    (0 : H) ∈ normal_ball R x := ⟨hx,fun _ _ => by simp⟩

theorem normal_ball_interior_zero (R : ℝ) {x n : H}
    (hx : x ∈ Metric.ball (0 : H) R) (hn : n ∈ normal_ball R x) : n=0 := by
  have hmax : IsLocalMax (fun z : H => inner ℝ n (z-x)) x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    have h := hn.2 z (Metric.ball_subset_closedBall hz)
    rw [real_inner_comm] at h
    simpa only [sub_self,inner_zero_right] using h
  have hl : HasFDerivAt (fun z : H => inner ℝ n (z-x)) ((InnerProductSpace.toDual ℝ H) n) x := by
    simpa only [inner_sub_right,InnerProductSpace.toDual_apply_apply] using
      (((InnerProductSpace.toDual ℝ H) n).hasFDerivAt.sub_const (inner ℝ n x))
  have he := hmax.hasFDerivAt_eq_zero hl
  apply (InnerProductSpace.toDual ℝ H).injective
  simpa using he

/-- Maximality of all sufficiently large normal-ball cutoffs implies original maximality. -/
theorem maximal_of_normal_ball_sums (A : H → Set H) (hA : IsMonotoneOp A)
    (R₀ : ℝ) (hmax : ∀ R : ℝ, R₀ < R → IsMaximalMonotone (opAdd A (normal_ball R))) :
    IsMaximalMonotone A := by
  refine ⟨hA,?_⟩
  intro A' hA' hsub
  funext x
  ext g
  constructor
  · intro hg
    let R : ℝ := |R₀|+‖x‖+1
    have hR : R₀ < R := by dsimp [R]; nlinarith [le_abs_self R₀,norm_nonneg x]
    have hx : x ∈ Metric.ball (0 : H) R := by
      rw [Metric.mem_ball,dist_zero_right]
      dsimp [R]; nlinarith [abs_nonneg R₀]
    have hsum : g ∈ opAdd A (normal_ball R) x := by
      apply BregmanPPACodex.maximal_related_point _ (hmax R hR) x g
      intro y w hw
      obtain ⟨a,ha,n,hn,rfl⟩ := hw
      have hp := hA' x y g a hg (hsub y ha)
      have hn' := normal_ball_monotone R x y 0 n
        (normal_ball_zero_mem R (Metric.ball_subset_closedBall hx)) hn
      simp only [zero_sub,inner_neg_right] at hn'
      rw [show g-(a+n)=(g-a)-n by abel,inner_sub_right]
      linarith
    obtain ⟨a,ha,n,hn,he⟩ := hsum
    have hn0 := normal_ball_interior_zero R hx hn
    rw [hn0,add_zero] at he
    exact he.symm ▸ ha
  · intro hg; exact hsub x hg
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- A continuous monotone field pointing strictly outward on a sphere has a zero inside it. -/
theorem zero_of_outward_sphere (F : H → H) (hf : Continuous F)
    (hm : ∀ x y : H, 0 ≤ inner ℝ (x-y) (F x-F y)) (R : ℝ) (hR : 0 < R)
    (hout : ∀ x : H, ‖x‖=R → 0 < inner ℝ (F x) x) :
    ∃ x ∈ Metric.ball (0 : H) R, F x=0 := by
  have h0 : (0 : H) ∈ Metric.closedBall (0 : H) R := by
    simp only [Metric.mem_closedBall,dist_self]; exact hR.le
  obtain ⟨x,hx,hvi⟩ := compact_primal_vi F (Metric.closedBall (0 : H) R)
    (isCompact_closedBall 0 R) (convex_closedBall 0 R) ⟨0,h0⟩ hf.continuousOn
    (fun x _ y _ => hm x y)
  have hp : inner ℝ (F x) x ≤ 0 := by
    have h := hvi 0 h0
    simp only [zero_sub,inner_neg_right] at h
    linarith
  have hne : ‖x‖ ≠ R := fun he => (not_lt_of_ge hp) (hout x he)
  have hle : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hxb : x ∈ Metric.ball (0 : H) R := by
    rw [Metric.mem_ball,dist_zero_right]
    exact lt_of_le_of_ne hle hne
  have hn : -F x ∈ normal_ball R x := by
    refine ⟨hx,?_⟩
    intro z hz
    have h := hvi z hz
    rw [inner_neg_right,real_inner_comm]
    linarith
  exact ⟨x,hxb,neg_eq_zero.mp (normal_ball_interior_zero R hxb hn)⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- The centered bounded-domain sum has a regularized zero. -/
theorem centered_sum_regularized_zero (A B : H → Set H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) (hA0 : (0 : H) ∈ A 0)
    (R δ K : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hbound : ∀ x b, b ∈ B x → ‖x‖ ≤ R)
    (hlocal : ∀ x ∈ Metric.ball (0 : H) δ, ∃ b ∈ B x, ‖b‖ ≤ K) :
    ∃ x a b : H, a ∈ A x ∧ b ∈ B x ∧ x+a+b=0 := by
  let d : ℝ := 1/2
  have hd : 0 < d := by norm_num [d]
  obtain ⟨JA,hJA,hAm,hAs⟩ := inverse_field_exists A hA d hd
  obtain ⟨JB,hJB,hBm,hBs⟩ := inverse_field_exists B hB d hd
  let F : H → H := fun v => -JA (-v)+JB v
  have hF : Continuous F := (hJA.comp continuous_neg).neg.add hJB
  have hmono : ∀ v w : H, 0 ≤ inner ℝ (v-w) (F v-F w) := by
    intro v w
    have ha := hAs (-v) (-w)
    have hb := hBs v w
    have heA : inner ℝ (v-w) (-JA (-v)- -JA (-w)) =
        inner ℝ (JA (-v)-JA (-w)) (-v- -w) := by
      rw [show -JA (-v)- -JA (-w)=-(JA (-v)-JA (-w)) by abel,
        show -v- -w=-(v-w) by abel]
      simp only [inner_neg_right,inner_neg_left]
      rw [real_inner_comm]
    have heB : inner ℝ (v-w) (JB v-JB w) = inner ℝ (JB v-JB w) (v-w) := real_inner_comm _ _
    have hmA : 0 ≤ inner ℝ (v-w) (-JA (-v)- -JA (-w)) := by
      rw [heA]; nlinarith [mul_nonneg hd.le (sq_nonneg ‖JA (-v)-JA (-w)‖)]
    have hmB : 0 ≤ inner ℝ (v-w) (JB v-JB w) := by
      rw [heB]; nlinarith [mul_nonneg hd.le (sq_nonneg ‖JB v-JB w‖)]
    have heF : F v-F w=(-JA (-v)- -JA (-w))+(JB v-JB w) := by dsimp [F]; abel
    rw [heF,inner_add_right]; exact add_nonneg hmA hmB
  have hnonneg (v : H) : 0 ≤ inner ℝ (-JA (-v)) v := by
    have h := hA.1 (JA (-v)) 0 (-v-d • JA (-v)) 0 (hAm (-v)) hA0
    simp only [sub_zero,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,
      inner_neg_right] at h
    rw [inner_neg_left]
    nlinarith [mul_nonneg hd.le (sq_nonneg ‖JA (-v)‖)]
  let C : ℝ := d*(δ/2)*R+(R+δ/2)*K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let L : ℝ := 2*(C+1)/δ
  have hL : 0 < L := div_pos (by positivity) hδ
  have hcalc : (δ/2)*L=C+1 := by dsimp [L]; field_simp
  have hout : ∀ v : H, ‖v‖=L → 0 < inner ℝ (F v) v := by
    intro v hv
    have hb := inverse_pairing_lower B hB.1 JB d R δ K hd.le hR hδ hK hBm hbound hlocal v
      (by rw [hv]; exact hL)
    have ha := hnonneg v
    rw [show (δ/2)*‖v‖-d*(δ/2)*R-(R+δ/2)*K=(δ/2)*‖v‖-C by dsimp [C]; ring] at hb
    rw [hv,hcalc] at hb
    dsimp [F]; rw [inner_add_left]
    linarith
  obtain ⟨v,_,hv⟩ := zero_of_outward_sphere F hF hmono L hL hout
  have heq : JA (-v)=JB v := by
    have hdiff : JB v-JA (-v)=0 := by simpa only [F,sub_eq_add_neg,add_comm] using hv
    exact (sub_eq_zero.mp hdiff).symm
  have ha := hAm (-v)
  rw [heq] at ha
  refine ⟨JB v,-v-d • JB v,v-d • JB v,ha,hBm v,?_⟩
  dsimp [d]; module
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

def shift_operator (A : H → Set H) (p q : H) : H → Set H :=
  fun x => {v | v+q ∈ A (x+p)}

theorem shift_monotone (A : H → Set H) (hA : IsMonotoneOp A) (p q : H) :
    IsMonotoneOp (shift_operator A p q) := by
  intro x y u v hu hv
  have h := hA (x+p) (y+p) (u+q) (v+q) hu hv
  rw [show x+p-(y+p)=x-y by abel,show u+q-(v+q)=u-v by abel] at h
  exact h

theorem shift_maximal (A : H → Set H) (hA : IsMaximalMonotone A) (p q : H) :
    IsMaximalMonotone (shift_operator A p q) := by
  refine ⟨shift_monotone A hA.1 p q,?_⟩
  intro A' hA' hsub
  funext x
  ext g
  constructor
  · intro hg
    apply BregmanPPACodex.maximal_related_point A hA (x+p) (g+q)
    intro y u hu
    have hm : u-q ∈ shift_operator A p q (y-p) := by
      simpa only [shift_operator,Set.mem_setOf_eq,sub_add_cancel] using hu
    have h := hA' x (y-p) g (u-q) hg (hsub _ hm)
    have h1 : x-(y-p)=(x+p)-y := by abel
    have h2 : g-(u-q)=(g+q)-u := by abel
    rwa [h1,h2] at h
  · intro hg; exact hsub x hg

theorem sum_monotone (A B : H → Set H) (hA : IsMonotoneOp A) (hB : IsMonotoneOp B) :
    IsMonotoneOp (opAdd A B) := by
  rintro x y u v ⟨a,ha,b,hb,rfl⟩ ⟨a',ha',b',hb',rfl⟩
  have h1 := hA x y a a' ha ha'
  have h2 := hB x y b b' hb hb'
  rw [show a+b-(a'+b')=(a-a')+(b-b') by abel,inner_add_right]
  exact add_nonneg h1 h2

theorem operator_sum_comm (A B : H → Set H) : opAdd A B=opAdd B A := by
  funext x
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩; exact ⟨b,hb,a,ha,add_comm _ _⟩
  · rintro ⟨b,hb,a,ha,rfl⟩; exact ⟨a,ha,b,hb,add_comm _ _⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem bounded_domain_sum_maximal (A B : H → Set H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x b, b ∈ B x → ‖x‖ ≤ R)
    (x₀ a₀ : H) (ha₀ : a₀ ∈ A x₀) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hlocal : ∀ x ∈ Metric.ball x₀ δ, ∃ b ∈ B x, ‖b‖ ≤ K) :
    IsMaximalMonotone (opAdd A B) := by
  have hm := sum_monotone A B hA.1 hB.1
  apply (gdr_max_iff (opAdd A B) hm 1 one_pos).mpr
  intro w
  let q := w-x₀-a₀
  let A' := shift_operator A x₀ a₀
  let B' := shift_operator B x₀ q
  have hA' : IsMaximalMonotone A' := shift_maximal A hA x₀ a₀
  have hB' : IsMaximalMonotone B' := shift_maximal B hB x₀ q
  have ha' : (0 : H) ∈ A' 0 := by simpa only [A',shift_operator,Set.mem_setOf_eq,zero_add] using ha₀
  have hbound' : ∀ x b, b ∈ B' x → ‖x‖ ≤ R+‖x₀‖ := by
    intro x b hb
    have h := hbound (x+x₀) (b+q) hb
    calc
      ‖x‖ = ‖(x+x₀)-x₀‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖x+x₀‖+‖x₀‖ := norm_sub_le _ _
      _ ≤ R+‖x₀‖ := by linarith
  have hlocal' : ∀ x ∈ Metric.ball (0 : H) δ, ∃ b ∈ B' x, ‖b‖ ≤ K+‖q‖ := by
    intro x hx
    have hx' : x+x₀ ∈ Metric.ball x₀ δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero] using hx
    obtain ⟨b,hb,hbK⟩ := hlocal (x+x₀) hx'
    refine ⟨b-q,?_,(norm_sub_le b q).trans (by linarith)⟩
    simpa only [B',shift_operator,Set.mem_setOf_eq,sub_add_cancel] using hb
  obtain ⟨x,a,b,ha,hb,he⟩ := centered_sum_regularized_zero A' B' hA' hB' ha'
    (R+‖x₀‖) δ (K+‖q‖) (by positivity) hδ (by positivity) hbound' hlocal'
  refine ⟨x+x₀,(a+a₀)+(b+q),⟨a+a₀,ha,b+q,hb,rfl⟩,?_⟩
  rw [one_smul]
  symm
  calc
    (x+x₀)+((a+a₀)+(b+q))=(x+a+b)+w := by dsimp [q]; abel
    _=w := by rw [he,zero_add]
end BregmanExistenceCodex

end

section

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 209: a *proper convex function* on a real normed space `V` is a
function `f : V → (−∞, +∞]`, not identically `+∞`, such that
`f((1 − λ)x + λy) ≤ (1 − λ)f(x) + λf(y)` whenever `x, y ∈ V` and `0 < λ < 1`.
The value set `(−∞, +∞]` is encoded as `EReal` together with the requirement that `f`
never takes the value `⊥ = −∞`. -/
def ProperConvex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (∃ x, f x ≠ ⊤) ∧
    ∀ (x y : V) (t : ℝ), 0 < t → t < 1 →
      f ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y

end RockafellarMaxMono.Shared


namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 209: the *subdifferential* of `f : V → (−∞, +∞]` at `x` is
`∂f(x) = {x* ∈ V* | f(y) ≥ f(x) + ⟨y − x, x*⟩ for all y ∈ V}`, a subset of the
(strong) dual `V* = StrongDual ℝ V`; the pairing `⟨y − x, x*⟩` is `x' (y - x)`. -/
def subdiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) (x : V) :
    Set (StrongDual ℝ V) :=
  {x' | ∀ y : V, f x + ((x' (y - x) : ℝ) : EReal) ≤ f y}

end RockafellarMaxMono.Shared


namespace RockafellarMaxMono.Maximality

/-- Rockafellar (1970), p. 209: a multivalued mapping `T : V → V*` (encoded as
`V → Set (StrongDual ℝ V)`) is a *monotone operator* if
`⟨x₀ − x₁, x₀* − x₁*⟩ ≥ 0` whenever `x₀* ∈ T(x₀)` and `x₁* ∈ T(x₁)`. -/
def IsMonotoneOp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  ∀ (x₀ x₁ : V) (x₀' x₁' : StrongDual ℝ V), x₀' ∈ T x₀ → x₁' ∈ T x₁ →
    0 ≤ (x₀' - x₁') (x₀ - x₁)

/-- Rockafellar (1970), p. 209: a monotone operator `T : V → V*` is *maximal monotone* if its
graph `G(T) = {(x, x*) | x* ∈ T(x)}` is not properly contained in the graph of any other
monotone operator `T' : V → V*`; equivalently, every monotone `T'` whose graph contains the
graph of `T` coincides with `T`. -/
def IsMaximalMonotone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  IsMonotoneOp T ∧
    ∀ T' : V → Set (StrongDual ℝ V), IsMonotoneOp T' → (∀ x, T x ⊆ T' x) → ∀ x, T' x = T x

end RockafellarMaxMono.Maximality

set_option autoImplicit false

/-- Ekeland's variational principle (weak form, with control of the value). -/
theorem rmm_ekeland {X : Type*} [MetricSpace X] [CompleteSpace X] (H : X → ℝ)
    (hH : LowerSemicontinuous H) (m : ℝ) (hm : ∀ x, m ≤ H x) (δ : ℝ) (hδ : 0 < δ) (x₁ : X) :
    ∃ x, H x ≤ H x₁ ∧ ∀ y, H x ≤ H y + δ * dist y x := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : X → Set X, ∀ z y, y ∈ S z ↔ H y + δ * dist y z ≤ H z :=
    ⟨fun z => {y | H y + δ * dist y z ≤ H z}, fun _ _ => Iff.rfl⟩
  have hself : ∀ z, z ∈ S z := by intro z; rw [hS]; simp
  have htrans : ∀ z y w, y ∈ S z → w ∈ S y → w ∈ S z := by
    intro z y w hy hw
    rw [hS] at hy hw ⊢
    have := dist_triangle w y z
    nlinarith
  have hclosed : ∀ z, IsClosed (S z) := by
    intro z
    have h1 : LowerSemicontinuous (fun y => H y + δ * dist y z) :=
      hH.add (Continuous.lowerSemicontinuous (by fun_prop))
    have h2 : S z = (fun y => H y + δ * dist y z) ⁻¹' Set.Iic (H z) := by
      ext y; rw [hS]; rfl
    rw [h2]
    exact h1.isClosed_preimage (H z)
  have hnext : ∀ z, ∃ y ∈ S z, ∀ w ∈ S y, δ * dist w y ≤ H z - H y := by
    intro z
    have hne : (H '' S z).Nonempty := ⟨H z, z, hself z, rfl⟩
    have hbdd : BddBelow (H '' S z) := ⟨m, by rintro _ ⟨y, -, rfl⟩; exact hm y⟩
    have hμ : sInf (H '' S z) ≤ H z := csInf_le hbdd ⟨z, hself z, rfl⟩
    obtain ⟨y, hy, hyμ⟩ : ∃ y ∈ S z, 2 * H y - H z ≤ sInf (H '' S z) := by
      rcases eq_or_lt_of_le hμ with h | h
      · exact ⟨z, hself z, by linarith⟩
      · obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
          (show sInf (H '' S z) < (H z + sInf (H '' S z)) / 2 by linarith)
        exact ⟨y, hy, by linarith⟩
    refine ⟨y, hy, fun w hw => ?_⟩
    have hwz : w ∈ S z := htrans z y w hy hw
    have hw' : sInf (H '' S z) ≤ H w := csInf_le hbdd ⟨w, hwz, rfl⟩
    rw [hS] at hw
    linarith
  choose nxt hnxtS hnxt using hnext
  obtain ⟨z, hz0, hzs⟩ : ∃ z : ℕ → X, z 0 = x₁ ∧ ∀ n, z (n + 1) = nxt (z n) :=
    ⟨fun n => Nat.rec x₁ (fun _ p => nxt p) n, rfl, fun _ => rfl⟩
  have hstep : ∀ n, z (n + 1) ∈ S (z n) := fun n => by rw [hzs]; exact hnxtS _
  have hnest : ∀ n k, n ≤ k → S (z k) ⊆ S (z n) := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hnk ih => exact fun w hw => ih (htrans _ _ _ (hstep k) hw)
  have hmem : ∀ n k, n ≤ k → z k ∈ S (z n) := fun n k hnk => hnest n k hnk (hself _)
  have hanti : Antitone (fun n => H (z n)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    have h1 := hstep n
    rw [hS] at h1
    have := dist_nonneg (x := z (n + 1)) (y := z n)
    nlinarith
  have hbddz : BddBelow (Set.range fun n => H (z n)) := ⟨m, by rintro _ ⟨n, rfl⟩; exact hm _⟩
  have hlimH := tendsto_atTop_ciInf hanti hbddz
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ⨅ n, H (z n) := ⟨_, rfl⟩
  rw [← hL] at hlimH
  have hLle : ∀ n, L ≤ H (z n) := fun n => hL ▸ ciInf_le hbddz n
  have hgap : ∀ n, ∀ w ∈ S (z (n + 1)), δ * dist w (z (n + 1)) ≤ H (z n) - L := by
    intro n w hw
    have h1 := hnxt (z n) w (by rw [← hzs]; exact hw)
    rw [← hzs] at h1
    linarith [hLle (n + 1)]
  have he : Filter.Tendsto (fun n => H (z n) - L) Filter.atTop (nhds 0) := by
    simpa using hlimH.sub_const L
  have hcauchy : CauchySeq z := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev := he.eventually (gt_mem_nhds (show (0:ℝ) < δ * ε by positivity))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N + 1, fun n hn => ?_⟩
    have h1 := hgap N (z n) (hmem (N + 1) n hn)
    have h2 := hN N le_rfl
    have h3 : δ * dist (z n) (z (N + 1)) < δ * ε := by linarith
    exact lt_of_mul_lt_mul_left h3 hδ.le
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxS : ∀ n, x ∈ S (z n) := fun n =>
    (hclosed _).mem_of_tendsto hx (Filter.eventually_atTop.2 ⟨n, fun k hk => hmem n k hk⟩)
  refine ⟨x, ?_, fun y => ?_⟩
  · have h1 := hxS 0
    rw [hS, hz0] at h1
    have := dist_nonneg (x := x) (y := x₁)
    nlinarith
  · by_contra hlt
    push Not at hlt
    have hyx : y ∈ S x := by rw [hS]; exact hlt.le
    have hbound : ∀ n, δ * dist y x ≤ 2 * (H (z n) - L) := by
      intro n
      have h1 := hgap n y (htrans _ _ _ (hxS (n + 1)) hyx)
      have h2 := hgap n x (hxS (n + 1))
      have h3 := dist_triangle y (z (n + 1)) x
      rw [dist_comm (z (n + 1)) x] at h3
      nlinarith
    have h0 : δ * dist y x ≤ 0 := by
      have h4 := he.const_mul 2
      simp only [mul_zero] at h4
      exact ge_of_tendsto' h4 hbound
    have hd : dist y x = 0 :=
      le_antisymm (by nlinarith [dist_nonneg (x := y) (y := x)]) dist_nonneg
    rw [dist_eq_zero] at hd
    subst hd
    simp at hlt

open RockafellarMaxMono in
theorem rmm_le_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (y : E) (r : ℝ) :
    f y ≤ (r : EReal) ↔ f y ≠ ⊤ ∧ (f y).toReal ≤ r := by
  constructor
  · intro h
    have hne : f y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) h
    refine ⟨hne, ?_⟩
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne (hf.1 y)]
    exact h
  · rintro ⟨hne, h⟩
    rw [← EReal.coe_toReal hne (hf.1 y)]
    exact EReal.coe_le_coe_iff.2 h

open RockafellarMaxMono in
theorem rmm_conv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (x y : E) (r s a b : ℝ) (hx : f x ≤ (r : EReal))
    (hy : f y ≤ (s : EReal)) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * r + b * s : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hx
  rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with hb1 | hb1
  · subst hb1
    have ha0 : a = 0 := by linarith
    subst ha0
    simpa using hy
  have ha' : a = 1 - b := by linarith
  subst ha'
  obtain ⟨hx1, hx2⟩ := (rmm_le_coe f hf x r).1 hx
  obtain ⟨hy1, hy2⟩ := (rmm_le_coe f hf y s).1 hy
  obtain ⟨p, hp, hpr⟩ : ∃ p : ℝ, f x = p ∧ p ≤ r :=
    ⟨_, (EReal.coe_toReal hx1 (hf.1 x)).symm, hx2⟩
  obtain ⟨q, hq, hqs⟩ : ∃ q : ℝ, f y = q ∧ q ≤ s :=
    ⟨_, (EReal.coe_toReal hy1 (hf.1 y)).symm, hy2⟩
  have hc := hf.2.2 x y b hbpos hb1
  rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hc
  refine hc.trans (EReal.coe_le_coe_iff.2 ?_)
  have h1 : 0 ≤ 1 - b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hpr h1, mul_le_mul_of_nonneg_left hqs hbpos.le]

open RockafellarMaxMono in
theorem rmm_epi_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (ψ : StrongDual ℝ E) (κ : ℝ) :
    Convex ℝ {p : E × ℝ | f p.1 ≤ ((p.2 + ψ p.1 + κ : ℝ) : EReal)} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  have h := rmm_conv_le f hf p.1 q.1 _ _ a b hp hq ha hb hab
  have heq : (a • p + b • q).2 + ψ (a • p + b • q).1 + κ
      = a * (p.2 + ψ p.1 + κ) + b * (q.2 + ψ q.1 + κ) := by
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_add,
      map_smul]
    linear_combination (-κ) * hab
  rw [heq]
  simpa only [Prod.fst_add, Prod.smul_fst] using h

theorem rmm_epi_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hlsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  have h := hlsc.isClosed_epigraph
  exact h.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

open RockafellarMaxMono in
theorem rmm_minorant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∃ (a : StrongDual ℝ E) (b : ℝ), ∀ x, f x ≠ ⊤ → a x + b ≤ (f x).toReal := by
  obtain ⟨x1, hx1⟩ := hf.2.1
  have hconv : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    have := rmm_epi_convex f hf 0 0
    simpa using this
  have hnot : ((x1, (f x1).toReal - 1) : E × ℝ) ∉ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro h
    simp only [Set.mem_ofPred_eq] at h
    rw [rmm_le_coe f hf] at h
    linarith [h.2]
  obtain ⟨ℓ, u, hℓ0, hℓ⟩ := geometric_hahn_banach_point_closed hconv (rmm_epi_closed f hlsc) hnot
  have hdec : ∀ (y : E) (r : ℝ), ℓ (y, r) = ℓ (y, 0) + r * ℓ (0, 1) := by
    intro y r
    have : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hmem : ∀ y, f y ≠ ⊤ →
      ((y, (f y).toReal) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro y hy
    simp only [Set.mem_ofPred_eq]
    rw [EReal.coe_toReal hy (hf.1 y)]
  have h1 := hℓ _ (hmem x1 hx1)
  rw [hdec] at h1 hℓ0
  have hc : 0 < ℓ (0, 1) := by nlinarith
  refine ⟨-(ℓ (0, 1))⁻¹ • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), u / ℓ (0, 1), fun x hx => ?_⟩
  have h2 := hℓ _ (hmem x hx)
  rw [hdec] at h2
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, smul_eq_mul]
  have e : -(ℓ (0, 1))⁻¹ * ℓ (x, 0) + u / ℓ (0, 1) = (u - ℓ (x, 0)) / ℓ (0, 1) := by
    field_simp
    ring
  rw [e, div_le_iff₀ hc]
  linarith

open RockafellarMaxMono in
theorem rmm_subdiff_fin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (x : E) (x' : StrongDual ℝ E) (h : x' ∈ Shared.subdiff f x) :
    f x ≠ ⊤ := by
  intro hx
  obtain ⟨z, hz⟩ := hf.2.1
  have h1 := (show ∀ y, f x + ((x' (y - x) : ℝ) : EReal) ≤ f y from h) z
  rw [hx, EReal.top_add_coe] at h1
  exact hz (top_le_iff.1 h1)

open RockafellarMaxMono in
theorem rmm_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x0 : E) (x0' : StrongDual ℝ E)
    (hrel : ∀ x, ∀ u ∈ Shared.subdiff f x, 0 ≤ (u - x0') (x - x0))
    (η : ℝ) (hη : 0 < η) :
    f x0 ≠ ⊤ ∧ ∀ y, f y ≠ ⊤ →
      (f x0).toReal + x0' (y - x0) - η * (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2) ≤ (f y).toReal := by
  classical
  obtain ⟨a, b, hab⟩ := rmm_minorant f hf hlsc
  obtain ⟨x1, hx1⟩ := hf.2.1
  have hfF : ∀ x, f x ≠ ⊤ → f x = (((f x).toReal : ℝ) : EReal) :=
    fun x hx => (EReal.coe_toReal hx (hf.1 x)).symm
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨k, hk⟩ : ∃ k : E → ℝ, ∀ x, k x = η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hkcont : Continuous k := by
    have : k = fun x => η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 := funext hk
    rw [this]; fun_prop
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, ∀ x, g x = (f x).toReal - x0' (x - x0) := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = g x1 + k x1 + 1 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : E → ℝ, ∀ x, H x = if f x = ⊤ then M else min (g x + k x) M :=
    ⟨_, fun _ => rfl⟩
  -- lower semicontinuity of the truncated function
  have hHlsc : LowerSemicontinuous H := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    by_cases hc : M ≤ c
    · have : H ⁻¹' Set.Iic c = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        rw [hH]
        split_ifs
        · exact hc
        · exact (min_le_right _ _).trans hc
      rw [this]; exact isClosed_univ
    · push Not at hc
      have : H ⁻¹' Set.Iic c = (fun x => ((x, c + x0' (x - x0) - k x) : E × ℝ)) ⁻¹'
          {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
        rw [rmm_le_coe f hf, hH]
        split_ifs with hx
        · simp only [hx, ne_eq, not_true_eq_false, false_and, iff_false, not_le]
          exact hc
        · rw [min_le_iff, hg]
          constructor
          · rintro (h | h)
            · exact ⟨hx, by linarith⟩
            · linarith
          · rintro ⟨-, h⟩
            left; linarith
      rw [this]
      exact (rmm_epi_closed f hlsc).preimage (continuous_id.prodMk
        ((continuous_const.add (x0'.continuous.comp (continuous_id.sub continuous_const))).sub
          hkcont))
  -- lower bound
  have hHbdd : ∀ x, min (a x0 + b - ‖a - x0'‖ ^ 2 / (4 * η)) M ≤ H x := by
    intro x
    rw [hH x]
    split_ifs with hx
    · exact min_le_right _ _
    · refine min_le_min_right _ ?_
      have h1 := hab x hx
      rw [hg, hk]
      have h2 := (a - x0').le_opNorm (x - x0)
      have h3 := neg_abs_le ((a - x0') (x - x0))
      rw [← Real.norm_eq_abs] at h3
      have h4 : (a - x0') (x - x0) = a x - a x0 - x0' (x - x0) := by
        rw [ContinuousLinearMap.sub_apply, map_sub]
      have hβ : ‖a - x0'‖ ^ 2 / (4 * η) * (4 * η) = ‖a - x0'‖ ^ 2 := by
        field_simp
      have ht := norm_nonneg (x - x0)
      have hC := norm_nonneg (a - x0')
      nlinarith [sq_nonneg (2 * η * ‖x - x0‖ - ‖a - x0'‖), mul_nonneg hη.le ht]
  -- Ekeland point
  obtain ⟨x, hxH, hxE⟩ := rmm_ekeland H hHlsc _ hHbdd δ hδpos x1
  have hH1 : H x1 = g x1 + k x1 := by
    rw [hH, if_neg hx1, min_eq_left (by rw [hM]; linarith)]
  rw [hH1] at hxH
  have hxfin : f x ≠ ⊤ := by
    intro hx
    rw [hH, if_pos hx] at hxH
    rw [hM] at hxH
    linarith
  have hHx : H x = g x + k x := by
    have hxH' := hxH
    rw [hH, if_neg hxfin] at hxH' ⊢
    rcases min_choice (g x + k x) M with h | h
    · exact h
    · rw [h] at hxH'; rw [hM] at hxH'; linarith
  have hEk : ∀ y, f y ≠ ⊤ → g x + k x ≤ g y + k y + δ * ‖y - x‖ := by
    intro y hy
    have h1 := hxE y
    rw [hHx, dist_eq_norm] at h1
    have h2 : H y ≤ g y + k y := by rw [hH, if_neg hy]; exact min_le_left _ _
    linarith
  -- the perturbation
  obtain ⟨K, hK⟩ : ∃ K : E → ℝ, ∀ y, K y = k y + δ * ‖y - x‖ := ⟨_, fun _ => rfl⟩
  have hKcont : Continuous K := by
    have : K = fun y => k y + δ * ‖y - x‖ := funext hK
    rw [this]; fun_prop
  have hKx : K x = k x := by rw [hK, sub_self, norm_zero, mul_zero, add_zero]
  have hnc : ∀ (u v : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → ‖s • u + t • v‖ ≤ s * ‖u‖ + t * ‖v‖ := by
    intro u v s t hs ht
    calc ‖s • u + t • v‖ ≤ ‖s • u‖ + ‖t • v‖ := norm_add_le _ _
      _ = s * ‖u‖ + t * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have hKconv : ∀ (y z : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → s + t = 1 →
      K (s • y + t • z) ≤ s * K y + t * K z := by
    intro y z s t hs ht hst
    have e1 : s • y + t • z - x0 = s • (y - x0) + t • (z - x0) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    have e2 : s • y + t • z - x = s • (y - x) + t • (z - x) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    rw [hK, hK, hK, hk, hk, hk, e1, e2]
    have n1 := hnc (y - x0) (z - x0) s t hs ht
    have n2 := hnc (y - x) (z - x) s t hs ht
    have n0 := norm_nonneg (s • (y - x0) + t • (z - x0))
    have hsq : ‖s • (y - x0) + t • (z - x0)‖ ^ 2 ≤ s * ‖y - x0‖ ^ 2 + t * ‖z - x0‖ ^ 2 := by
      have h1 : ‖s • (y - x0) + t • (z - x0)‖ ^ 2 ≤ (s * ‖y - x0‖ + t * ‖z - x0‖) ^ 2 :=
        pow_le_pow_left₀ n0 n1 2
      have h2 : (s * ‖y - x0‖ + t * ‖z - x0‖) ^ 2 ≤ s * ‖y - x0‖ ^ 2 + t * ‖z - x0‖ ^ 2 := by
        have ht' : t = 1 - s := by linarith
        subst ht'
        nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (‖y - x0‖ - ‖z - x0‖))]
      linarith
    have m1 := mul_le_mul_of_nonneg_left n1 hη.le
    have m2 := mul_le_mul_of_nonneg_left hsq hη.le
    have m3 := mul_le_mul_of_nonneg_left n2 hδpos.le
    nlinarith
  -- the two convex sets
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = g x - x0' x0 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Set (E × ℝ), A = {p : E × ℝ | f p.1 ≤ ((p.2 + x0' p.1 + κ : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set (E × ℝ), B = {p : E × ℝ | p.2 < -(K p.1 - K x)} := ⟨_, rfl⟩
  have hAconv : Convex ℝ A := hA ▸ rmm_epi_convex f hf x0' κ
  have hBopen : IsOpen B := by
    rw [hB]
    exact isOpen_lt continuous_snd (((hKcont.comp continuous_fst).sub continuous_const).neg)
  have hBconv : Convex ℝ B := by
    rw [hB]
    intro p hp q hq s t hs ht hst
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    have hc := hKconv p.1 q.1 s t hs ht hst
    have hd1 : 0 < -(K p.1 - K x) - p.2 := by linarith
    have hd2 : 0 < -(K q.1 - K x) - q.2 := by linarith
    have hkey : 0 < s * (-(K p.1 - K x) - p.2) + t * (-(K q.1 - K x) - q.2) := by
      rcases eq_or_lt_of_le hs with hs0 | hspos
      · subst hs0
        have ht1 : t = 1 := by linarith
        subst ht1
        linarith
      · have := mul_pos hspos hd1
        have := mul_nonneg ht hd2.le
        linarith
    have hKx' : K x = s * K x + t * K x := by rw [← add_mul, hst, one_mul]
    nlinarith
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    intro p hpB hpA
    rw [hB] at hpB
    rw [hA] at hpA
    simp only [Set.mem_ofPred_eq] at hpB hpA
    rw [rmm_le_coe f hf] at hpA
    obtain ⟨hp1, hp2⟩ := hpA
    have h1 := hEk p.1 hp1
    rw [hK p.1, hKx] at hpB
    rw [hg p.1, hg x] at h1
    rw [hκ, hg x] at hp2
    simp only [map_sub] at h1 hp2
    linarith
  obtain ⟨ℓ, u, hℓB, hℓA⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  have hdec : ∀ (y : E) (r : ℝ), ℓ (y, r) = ℓ (y, 0) + r * ℓ (0, 1) := by
    intro y r
    have : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hlin : ∀ y z : E, ℓ (y - z, 0) = ℓ (y, 0) - ℓ (z, 0) := by
    intro y z
    have : ((y - z, (0 : ℝ)) : E × ℝ) = (y, 0) - (z, 0) := by ext <;> simp
    rw [this, map_sub]
  have hxA : ((x, 0) : E × ℝ) ∈ A := by
    rw [hA]
    simp only [Set.mem_ofPred_eq]
    rw [rmm_le_coe f hf]
    refine ⟨hxfin, ?_⟩
    rw [hκ, hg, map_sub]
    linarith
  have hxB : ((x, -1) : E × ℝ) ∈ B := by
    rw [hB]
    simp only [Set.mem_ofPred_eq, sub_self, neg_zero]
    norm_num
  have hu1 := hℓA _ hxA
  have hu2 := hℓB _ hxB
  rw [hdec] at hu2
  have hc : 0 < ℓ (0, 1) := by linarith
  have hu : u = ℓ (x, 0) := by
    by_contra hne
    have hlt : u < ℓ (x, 0) := lt_of_le_of_ne hu1 hne
    have hB' : ((x, (u - ℓ (x, 0)) / ℓ (0, 1)) : E × ℝ) ∈ B := by
      rw [hB]
      simp only [Set.mem_ofPred_eq, sub_self, neg_zero]
      exact div_neg_of_neg_of_pos (by linarith) hc
    have h1 := hℓB _ hB'
    rw [hdec, div_mul_cancel₀ _ hc.ne'] at h1
    linarith
  obtain ⟨ψ, hψ⟩ : ∃ ψ : StrongDual ℝ E, ∀ v, ψ v = -(ℓ (v, 0)) / ℓ (0, 1) :=
    ⟨-(ℓ (0, 1))⁻¹ • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), fun v => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, smul_eq_mul]
      field_simp⟩
  have hS1 : ∀ y, f y ≠ ⊤ → ψ (y - x) ≤ g y - g x := by
    intro y hy
    have hyA : ((y, g y - g x) : E × ℝ) ∈ A := by
      rw [hA]
      simp only [Set.mem_ofPred_eq]
      rw [rmm_le_coe f hf]
      refine ⟨hy, ?_⟩
      rw [hκ, hg y, hg x, map_sub, map_sub]
      linarith
    have h1 := hℓA _ hyA
    rw [hdec] at h1
    rw [hψ, hlin, div_le_iff₀ hc]
    linarith
  have hS2 : ∀ y, -ψ (y - x) ≤ K y - K x := by
    intro y
    by_contra hlt
    push Not at hlt
    have hyB : ((y, ψ (y - x)) : E × ℝ) ∈ B := by
      rw [hB]
      simp only [Set.mem_ofPred_eq]
      linarith
    have h1 := hℓB _ hyB
    rw [hdec, hψ, hlin, div_mul_cancel₀ _ hc.ne'] at h1
    linarith
  have hsub : ψ + x0' ∈ Shared.subdiff f x := by
    show ∀ y, f x + (((ψ + x0') (y - x) : ℝ) : EReal) ≤ f y
    intro y
    by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · rw [hfF x hxfin, hfF y hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h1 := hS1 y hy
      rw [hg, hg] at h1
      simp only [ContinuousLinearMap.add_apply, map_sub] at h1 ⊢
      linarith
  have hmono := hrel x _ hsub
  simp only [add_sub_cancel_right] at hmono
  have hx0 : x = x0 := by
    have h := hS2 x0
    have e1 : K x0 = δ * ‖x - x0‖ := by
      rw [hK, hk, sub_self, norm_zero, norm_sub_rev]; ring
    have e2 : K x = η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 := by rw [hKx, hk]
    rw [e1, e2, map_sub] at h
    rw [map_sub] at hmono
    have ht := norm_nonneg (x - x0)
    have h0 : ‖x - x0‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖x - x0‖ := lt_of_le_of_ne ht (Ne.symm hne)
      have := mul_pos hη hpos
      nlinarith [sq_nonneg ‖x - x0‖]
    rwa [norm_eq_zero, sub_eq_zero] at h0
  refine ⟨hx0 ▸ hxfin, fun y hy => ?_⟩
  have h1 := hS1 y hy
  have h2 := hS2 y
  rw [hK y, hKx, hk, hk] at h2
  rw [hx0] at h1 h2
  rw [hg, hg, sub_self, map_zero, sub_zero] at h1
  rw [sub_self, norm_zero] at h2
  have hw := norm_nonneg (y - x0)
  nlinarith [mul_nonneg hη.le hw]

open RockafellarMaxMono in
theorem rmm_key {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x0 : E) (x0' : StrongDual ℝ E)
    (hrel : ∀ x, ∀ u ∈ Shared.subdiff f x, 0 ≤ (u - x0') (x - x0)) :
    x0' ∈ Shared.subdiff f x0 := by
  have hfin := (rmm_step f hf hlsc x0 x0' hrel 1 one_pos).1
  show ∀ y, f x0 + ((x0' (y - x0) : ℝ) : EReal) ≤ f y
  intro y
  by_cases hy : f y = ⊤
  · rw [hy]; exact le_top
  rw [← EReal.coe_toReal hfin (hf.1 x0), ← EReal.coe_toReal hy (hf.1 y), ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hw : 0 ≤ ‖y - x0‖ := norm_nonneg _
  have hden : 0 < 2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1 := by positivity
  have h := (rmm_step f hf hlsc x0 x0' hrel (ε / (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1))
    (div_pos hε hden)).2 y hy
  have h3 : ε / (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1) * (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  linarith

open RockafellarMaxMono RockafellarMaxMono.Maximality in
theorem bregman_existence_accepted_subdiff_maximal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    IsMaximalMonotone (Shared.subdiff f) := by
  have hmono : IsMonotoneOp (Shared.subdiff f) := by
    intro x₀ x₁ x₀' x₁' h0 h1
    have hfin0 := rmm_subdiff_fin f hf x₀ x₀' h0
    have hfin1 := rmm_subdiff_fin f hf x₁ x₁' h1
    have a0 := (show ∀ y, f x₀ + ((x₀' (y - x₀) : ℝ) : EReal) ≤ f y from h0) x₁
    have a1 := (show ∀ y, f x₁ + ((x₁' (y - x₁) : ℝ) : EReal) ≤ f y from h1) x₀
    rw [← EReal.coe_toReal hfin0 (hf.1 x₀), ← EReal.coe_toReal hfin1 (hf.1 x₁),
      ← EReal.coe_add, EReal.coe_le_coe_iff] at a0 a1
    simp only [ContinuousLinearMap.sub_apply, map_sub] at a0 a1 ⊢
    linarith
  refine ⟨hmono, fun T' hT' hsub x => ?_⟩
  ext x'
  constructor
  · intro hx'
    exact rmm_key f hf hlsc x x' fun z u hu => hT' z x u x' (hsub z hu) hx'
  · intro hx'
    exact hsub x hx'


end

section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

lemma positive_coe_mul_ne_bot (a : ℝ) (ha : 0 ≤ a) (v : EReal) (hv : v ≠ ⊥) :
    (a : EReal)*v ≠ ⊥ :=
  (EReal.mul_ne_bot _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _),Or.inr hv,
    Or.inl (EReal.coe_ne_top _),Or.inl (EReal.coe_nonneg.mpr ha)⟩

/-- Bridge the original epigraph predicate to the inspected convex-combination helper. -/
theorem epigraph_proper_convex (f : H → EReal) (hp : IsProperFn f) (hc : IsConvexFn f) :
    RockafellarMaxMono.Shared.ProperConvex f := by
  refine ⟨hp.1,hp.2,?_⟩
  intro x y t ht ht1
  by_cases hx : f x=⊤
  · rw [hx,EReal.coe_mul_top_of_pos (sub_pos.mpr ht1),
      EReal.top_add_of_ne_bot (positive_coe_mul_ne_bot t ht.le (f y) (hp.1 y))]
    exact le_top
  by_cases hy : f y=⊤
  · rw [hy,EReal.coe_mul_top_of_pos ht,
      EReal.add_top_of_ne_bot (positive_coe_mul_ne_bot (1-t) (sub_nonneg.mpr ht1.le) (f x) (hp.1 x))]
    exact le_top
  have hxe : (x,(f x).toReal) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f x ≤ ((f x).toReal : EReal)
    rw [EReal.coe_toReal hx (hp.1 x)]
  have hye : (y,(f y).toReal) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f y ≤ ((f y).toReal : EReal)
    rw [EReal.coe_toReal hy (hp.1 y)]
  have hm := hc hxe hye (a := 1-t) (b := t) (sub_nonneg.mpr ht1.le) ht.le (by ring)
  change f ((1-t) • x+t • y) ≤ (((1-t)*(f x).toReal+t*(f y).toReal : ℝ) : EReal) at hm
  rw [EReal.coe_add,EReal.coe_mul,EReal.coe_mul,
    EReal.coe_toReal hx (hp.1 x),EReal.coe_toReal hy (hp.1 y)] at hm
  exact hm

/-- The original Hilbert subgradient is exactly the inspected dual predicate under Riesz. -/
theorem subgradient_riesz_iff (f : H → EReal)
    (hf : RockafellarMaxMono.Shared.ProperConvex f) (x g : H) :
    IsSubgradient f x g ↔ (InnerProductSpace.toDual ℝ H) g ∈ RockafellarMaxMono.Shared.subdiff f x := by
  constructor
  · intro h
    simpa only [RockafellarMaxMono.Shared.subdiff,Set.mem_setOf_eq,
      InnerProductSpace.toDual_apply_apply] using h.2
  · intro h
    refine ⟨rmm_subdiff_fin f hf x ((InnerProductSpace.toDual ℝ H) g) h,?_⟩
    simpa only [RockafellarMaxMono.Shared.subdiff,Set.mem_setOf_eq,
      InnerProductSpace.toDual_apply_apply] using h

/-- Maximal subdifferentials, with the exact original graph-inclusion and epigraph predicates. -/
theorem original_subdiff_maximal (f : H → EReal) (hp : IsProperFn f)
    (hc : IsConvexFn f) (hl : LowerSemicontinuous f) :
    IsMaximalMonotone (BregmanPPA.Convergence.subdiffOp f) := by
  have hf := epigraph_proper_convex f hp hc
  have hmono : IsMonotoneOp (BregmanPPA.Convergence.subdiffOp f) := by
    intro x y g v hg hv
    have h1 := BregmanPPACodex.subgradient_real_comparison f hp hg hv.1
    have h2 := BregmanPPACodex.subgradient_real_comparison f hp hv hg.1
    simp only [inner_sub_left,inner_sub_right] at h1 h2 ⊢
    simp only [real_inner_comm] at h1 h2 ⊢
    linarith
  refine ⟨hmono,?_⟩
  intro T' hT' hsub
  funext x
  ext g
  constructor
  · intro hg
    have hdual : (InnerProductSpace.toDual ℝ H) g ∈ RockafellarMaxMono.Shared.subdiff f x := by
      apply rmm_key f hf hl x ((InnerProductSpace.toDual ℝ H) g)
      intro z u hu
      have huf : IsSubgradient f z ((InnerProductSpace.toDual ℝ H).symm u) :=
        (subgradient_riesz_iff f hf z _).mpr (by simpa using hu)
      have hpair := hT' z x ((InnerProductSpace.toDual ℝ H).symm u) g (hsub z huf) hg
      have he : (u-(InnerProductSpace.toDual ℝ H) g) (z-x) =
          inner ℝ (z-x) ((InnerProductSpace.toDual ℝ H).symm u-g) := by
        rw [ContinuousLinearMap.sub_apply,← InnerProductSpace.toDual_symm_apply,
          InnerProductSpace.toDual_apply_apply]
        rw [← inner_sub_left,real_inner_comm]
      rw [he]
      exact hpair
    exact (subgradient_riesz_iff f hf x g).mpr hdual
  · intro hg; exact hsub x hg
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

noncomputable def restricted_real (C : Set H) (h : H → ℝ) : H → EReal := by
  classical
  exact fun x => if x ∈ C then (h x : EReal) else ⊤

theorem restricted_real_ne_bot (C : Set H) (h : H → ℝ) (x : H) :
    restricted_real C h x ≠ ⊥ := by
  classical
  by_cases hx : x ∈ C <;> simp [restricted_real,hx]

theorem restricted_real_mem_of_finite (C : Set H) (h : H → ℝ) {x : H}
    (hx : restricted_real C h x ≠ ⊤) : x ∈ C := by
  classical
  by_contra hn
  exact hx (by simp [restricted_real,hn])

theorem restricted_real_proper (C : Set H) (h : H → ℝ) (hne : C.Nonempty) :
    IsProperFn (restricted_real C h) := by
  classical
  obtain ⟨x,hx⟩ := hne
  exact ⟨restricted_real_ne_bot C h,⟨x,by simp [restricted_real,hx]⟩⟩

theorem restricted_real_convex (C : Set H) (h : H → ℝ) (hc : ConvexOn ℝ C h) :
    IsConvexFn (restricted_real C h) := by
  classical
  intro p hp q hq a b ha hb hab
  have hpC : p.1 ∈ C := by
    by_contra hn
    simp [restricted_real,hn] at hp
  have hqC : q.1 ∈ C := by
    by_contra hn
    simp [restricted_real,hn] at hq
  have hp' : h p.1 ≤ p.2 := by
    simpa only [Set.mem_setOf_eq,restricted_real,if_pos hpC,EReal.coe_le_coe_iff] using hp
  have hq' : h q.1 ≤ q.2 := by
    simpa only [Set.mem_setOf_eq,restricted_real,if_pos hqC,EReal.coe_le_coe_iff] using hq
  have hC := hc.1 hpC hqC ha hb hab
  have hf := hc.2 hpC hqC ha hb hab
  change restricted_real C h (a • p.1+b • q.1) ≤ ((a*p.2+b*q.2 : ℝ) : EReal)
  rw [restricted_real,if_pos hC,EReal.coe_le_coe_iff]
  calc
    h (a • p.1+b • q.1) ≤ a*h p.1+b*h q.1 := by simpa only [smul_eq_mul] using hf
    _ ≤ a*p.2+b*q.2 := add_le_add (mul_le_mul_of_nonneg_left hp' ha) (mul_le_mul_of_nonneg_left hq' hb)

theorem restricted_real_lsc (C : Set H) (h : H → ℝ) (hc : IsClosed C)
    (hh : ContinuousOn h C) : LowerSemicontinuous (restricted_real C h) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a=⊤
  · subst a; simp
  by_cases hb : a=⊥
  · subst a
    have he : (restricted_real C h) ⁻¹' Set.Iic (⊥ : EReal) = ∅ := by
      ext x
      simp only [Set.mem_preimage,Set.mem_Iic,le_bot_iff,Set.mem_empty_iff_false]
      exact iff_false_intro (restricted_real_ne_bot C h x)
    rw [he]; exact isClosed_empty
  have he : (restricted_real C h) ⁻¹' Set.Iic a = C ∩ h ⁻¹' Set.Iic a.toReal := by
    ext x
    by_cases hx : x ∈ C
    · simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_inter_iff]
      rw [show restricted_real C h x=(h x : EReal) by simp [restricted_real,hx]]
      have hab : (h x : EReal) ≤ a ↔ h x ≤ a.toReal := by
        conv_lhs => rw [← EReal.coe_toReal ha hb,EReal.coe_le_coe_iff]
      simpa only [hx,true_and] using hab
    · have ha' : ¬(⊤ : EReal) ≤ a := fun hn => ha (top_le_iff.mp hn)
      simp [restricted_real,hx,ha']
  rw [he]
  exact hh.preimage_isClosed_of_isClosed hc isClosed_Iic

noncomputable def closed_ball_extension (S : Set H) (h : H → ℝ) (R : ℝ) : H → EReal :=
  restricted_real (closure S ∩ Metric.closedBall 0 R) h

theorem closed_ball_subdiff_maximal (S : Set H) (h : H → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (R : ℝ)
    (hne : (closure S ∩ Metric.closedBall 0 R).Nonempty) :
    IsMaximalMonotone (BregmanPPA.Convergence.subdiffOp (closed_ball_extension S h R)) := by
  let C := closure S ∩ Metric.closedBall (0 : H) R
  have hc : IsClosed C := isClosed_closure.inter Metric.isClosed_closedBall
  have hcv : ConvexOn ℝ C h := by
    refine ⟨hh.strictConvexOn.convexOn.1.inter (convex_closedBall 0 R),?_⟩
    intro x hx y hy a b ha hb hab
    exact hh.strictConvexOn.convexOn.2 hx.1 hy.1 ha hb hab
  exact original_subdiff_maximal _ (restricted_real_proper C h hne)
    (restricted_real_convex C h hcv)
    (restricted_real_lsc C h hc (hh.continuousOn.mono Set.inter_subset_left))

theorem closed_ball_subdiff_domain (S : Set H) (h : H → ℝ) (R : ℝ) :
    dom (BregmanPPA.Convergence.subdiffOp (closed_ball_extension S h R)) ⊆
      Metric.closedBall 0 R := by
  rintro x ⟨g,hg⟩
  exact (restricted_real_mem_of_finite (closure S ∩ Metric.closedBall 0 R) h hg.1).2
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR Filter Topology
namespace BregmanExistenceCodex
open BregmanPPA.Convergence BregmanPPA.Existence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem closed_ball_subgradient_iff (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) (R : ℝ) {x g : H} (hx : x ∈ S) :
    IsSubgradient (closed_ball_extension S h R) x g ↔ g-gradient h x ∈ normal_ball R x := by
  classical
  let C := closure S ∩ Metric.closedBall (0 : H) R
  constructor
  · intro hg
    have hxC : x ∈ C := restricted_real_mem_of_finite C h hg.1
    refine ⟨hxC.2,?_⟩
    have hS : ∀ᶠ z in 𝓝[Metric.closedBall (0 : H) R] x, z ∈ S :=
      nhdsWithin_le_nhds (hh.isOpen.mem_nhds hx)
    have hmin : IsLocalMinOn (fun z : H => h z-inner ℝ g (z-x))
        (Metric.closedBall (0 : H) R) x := by
      filter_upwards [hS,self_mem_nhdsWithin] with z hzS hzB
      have hzC : z ∈ C := ⟨subset_closure hzS,hzB⟩
      have hs := hg.2 z
      change restricted_real C h x+((inner ℝ g (z-x) : ℝ) : EReal) ≤ restricted_real C h z at hs
      simp only [restricted_real,if_pos hxC,if_pos hzC] at hs
      rw [← EReal.coe_add,EReal.coe_le_coe_iff] at hs
      simp only [sub_self,inner_zero_right,sub_zero]
      linarith
    have hd : DifferentiableAt ℝ h x :=
      ((hh.contDiffOn.differentiableOn (by simp)) x hx).differentiableAt (hh.isOpen.mem_nhds hx)
    have hl : HasFDerivAt (fun z : H => inner ℝ g (z-x)) ((InnerProductSpace.toDual ℝ H) g) x := by
      simpa only [inner_sub_right,InnerProductSpace.toDual_apply_apply] using
        (((InnerProductSpace.toDual ℝ H) g).hasFDerivAt.sub_const (inner ℝ g x))
    intro z hz
    have ht : z-x ∈ posTangentConeAt (Metric.closedBall (0 : H) R) x :=
      sub_mem_posTangentConeAt_of_segment_subset ((convex_closedBall 0 R).segment_subset hxC.2 hz)
    have hs := hmin.hasFDerivWithinAt_nonneg (hd.hasFDerivAt.sub hl).hasFDerivWithinAt ht
    simp only [ContinuousLinearMap.sub_apply,InnerProductSpace.toDual_apply_apply] at hs
    rw [← inner_gradient_left] at hs
    rw [real_inner_comm,inner_sub_left]
    linarith
  · intro hn
    have hxC : x ∈ C := ⟨subset_closure hx,hn.1⟩
    refine ⟨?_,?_⟩
    · change restricted_real C h x ≠ ⊤
      simp [restricted_real,hxC]
    intro z
    by_cases hz : z ∈ C
    · have hs := BregmanPPACodex.gradient_support S h hh hx hz.1
      have hnormal := hn.2 z hz.2
      rw [real_inner_comm,inner_sub_left] at hnormal
      change restricted_real C h x+((inner ℝ g (z-x) : ℝ) : EReal) ≤ restricted_real C h z
      simp only [restricted_real,if_pos hxC,if_pos hz]
      rw [← EReal.coe_add,EReal.coe_le_coe_iff]
      linarith
    · change restricted_real C h x+((inner ℝ g (z-x) : ℝ) : EReal) ≤ restricted_real C h z
      simp [restricted_real,hz]

theorem clipped_sum_eq_normal_sum (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) (hdom : dom T ⊆ S) (R : ℝ) :
    opAdd (subdiffOp (closed_ball_extension S h R)) T =
      opAdd (opAdd (gradOp S h) T) (normal_ball R) := by
  funext x
  ext w
  constructor
  · rintro ⟨g,hg,v,hv,rfl⟩
    have hx := hdom (show x ∈ dom T from ⟨v,hv⟩)
    have hn := (closed_ball_subgradient_iff S h hh R hx).mp hg
    exact ⟨gradient h x+v,⟨gradient h x,⟨hx,rfl⟩,v,hv,rfl⟩,
      g-gradient h x,hn,by abel⟩
  · rintro ⟨a,⟨g,⟨hx,rfl⟩,v,hv,rfl⟩,n,hn,rfl⟩
    have hn' : gradient h x+n-gradient h x ∈ normal_ball R x := by
      simpa only [add_sub_cancel_left] using hn
    exact ⟨gradient h x+n,(closed_ball_subgradient_iff S h hh R hx).mpr hn',v,hv,by abel⟩

theorem clipped_subdiff_interior_fibre (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) (R : ℝ) {x g : H}
    (hx : x ∈ S) (hxB : x ∈ Metric.ball (0 : H) R) :
    IsSubgradient (closed_ball_extension S h R) x g ↔ g=gradient h x := by
  rw [closed_ball_subgradient_iff S h hh R hx]
  constructor
  · intro hg
    exact sub_eq_zero.mp (normal_ball_interior_zero R hxB hg)
  · intro hg
    rw [hg,sub_self]
    exact normal_ball_zero_mem R (Metric.ball_subset_closedBall hxB)
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanExistenceCodex
open BregmanPPA.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem original_gradient_continuous (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) {x : H} (hx : x ∈ S) :
    ContinuousAt (gradient h) x := by
  have hf := (hh.contDiffOn.contDiffAt (hh.isOpen.mem_nhds hx)).continuousAt_fderiv (by simp)
  change ContinuousAt (fun y => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ h y)) x
  simpa only [Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.continuousAt.comp hf

/-- Around any zone point strictly within a cutoff ball, clipped subgradients are locally bounded. -/
theorem clipped_subdiff_local_bound (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) (R : ℝ) {x₀ : H} (hx : x₀ ∈ S)
    (hxB : x₀ ∈ Metric.ball (0 : H) R) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧ ∀ x ∈ Metric.ball x₀ δ,
      ∃ g ∈ subdiffOp (closed_ball_extension S h R) x, ‖g‖ ≤ K := by
  let K : ℝ := ‖gradient h x₀‖+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht : Tendsto (fun x => ‖gradient h x‖) (𝓝 x₀) (𝓝 ‖gradient h x₀‖) :=
    (original_gradient_continuous S h hh hx).norm
  have hb : ∀ᶠ x in 𝓝 x₀, ‖gradient h x‖ < K :=
    ht.eventually (Iio_mem_nhds (by dsimp [K]; linarith))
  have hU : S ∩ Metric.ball (0 : H) R ∩ {x | ‖gradient h x‖ < K} ∈ 𝓝 x₀ :=
    inter_mem (inter_mem (hh.isOpen.mem_nhds hx) (Metric.isOpen_ball.mem_nhds hxB)) hb
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ,K,hδ,hK,?_⟩
  intro x hxδ
  have hp := hball hxδ
  refine ⟨gradient h x,?_,hp.2.le⟩
  exact (clipped_subdiff_interior_fibre S h hh R hp.1.1 hp.1.2).mpr rfl
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR BregmanPPA.Existence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem gradient_operator_monotone (S : Set H) (h : H → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h) : IsMonotoneOp (gradOp S h) := by
  rintro x y u v ⟨hx,rfl⟩ ⟨hy,rfl⟩
  have hxy := BregmanPPACodex.gradient_support S h hh hx (subset_closure hy)
  have hyx := BregmanPPACodex.gradient_support S h hh hy (subset_closure hx)
  rw [← neg_sub x y,inner_neg_right] at hxy
  rw [real_inner_comm] at hxy hyx
  rw [inner_sub_right]
  linarith

/-- Ball localization proves maximality under the original domain inclusion. -/
theorem gradient_sum_maximal (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ S) : IsMaximalMonotone (opAdd (gradOp S h) T) := by
  obtain ⟨x₀,a₀,ha₀,_⟩ := gdr_minty_core T hT 1 one_pos 0
  have hx₀ : x₀ ∈ S := hdom ⟨a₀,ha₀⟩
  apply maximal_of_normal_ball_sums _
    (sum_monotone _ _ (gradient_operator_monotone S h hh) hT.1) ‖x₀‖
  intro R hR
  have hR0 : 0 ≤ R := (norm_nonneg x₀).trans hR.le
  have hxB : x₀ ∈ Metric.ball (0 : H) R := by
    simpa only [Metric.mem_ball,dist_zero_right] using hR
  let B := BregmanPPA.Convergence.subdiffOp (closed_ball_extension S h R)
  have hB : IsMaximalMonotone B := closed_ball_subdiff_maximal S h hh R
    ⟨x₀,subset_closure hx₀,Metric.ball_subset_closedBall hxB⟩
  have hbound : ∀ x b, b ∈ B x → ‖x‖ ≤ R := by
    intro x b hb
    have hx := closed_ball_subdiff_domain S h R (show x ∈ dom B from ⟨b,hb⟩)
    simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  obtain ⟨δ,K,hδ,hK,hlocal⟩ := clipped_subdiff_local_bound S h hh R hx₀ hxB
  have hmax := bounded_domain_sum_maximal T B hT hB R hR0 hbound x₀ a₀ ha₀ δ K hδ hK hlocal
  rw [operator_sum_comm T B] at hmax
  change IsMaximalMonotone (opAdd (BregmanPPA.Convergence.subdiffOp
    (closed_ball_extension S h R)) T) at hmax
  rw [clipped_sum_eq_normal_sum T S h hh hdom R] at hmax
  exact hmax
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem scaled_operator_monotone (T : H → Set H) (hT : IsMonotoneOp T)
    (c : ℝ) (hc : 0 ≤ c) : IsMonotoneOp (opSmul c T) := by
  rintro x y u v ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
  rw [← smul_sub,inner_smul_right]
  exact mul_nonneg hc (hT x y a b ha hb)

theorem scaled_operator_maximal (T : H → Set H) (hT : IsMaximalMonotone T)
    (c : ℝ) (hc : 0 < c) : IsMaximalMonotone (opSmul c T) := by
  apply (gdr_max_iff _ (scaled_operator_monotone T hT.1 c hc.le) 1 one_pos).mpr
  intro w
  obtain ⟨x,a,ha,he⟩ := gdr_minty_core T hT c hc w
  exact ⟨x,c • a,⟨a,ha,rfl⟩,by simpa only [one_smul] using he⟩

theorem scaled_operator_domain (T : H → Set H) (c : ℝ) : dom (opSmul c T)=dom T := by
  ext x
  constructor
  · rintro ⟨w,a,ha,_⟩; exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩; exact ⟨c • a,a,ha,rfl⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR BregmanPPA.Existence
open scoped Pointwise
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem gradient_operator_image (S : Set H) (h : H → ℝ) :
    imOp (gradOp S h)=gradient h '' S := by
  ext y
  constructor
  · rintro ⟨x,hx,he⟩; exact ⟨x,hx,he.symm⟩
  · rintro ⟨x,hx,he⟩; exact ⟨x,hx,he.symm⟩

theorem original_image_inclusion (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ S)
    (hcase : gradient h '' S=Set.univ ∨ (IsOpen (gradient h '' S) ∧ (0 : H) ∈ imOp T))
    (c : ℝ) (hc : 0 < c) :
    gradient h '' S ⊆ imOp (opAdd (gradOp S h) (opSmul c T)) := by
  let A := opSmul c T
  let B := gradOp S h
  have hA : IsMaximalMonotone A := scaled_operator_maximal T hT c hc
  have hdA : dom A ⊆ S := by rw [scaled_operator_domain T c]; exact hdom
  have hd : dom A ⊆ dom B := by
    intro x hx
    exact ⟨gradient h x,hdA hx,rfl⟩
  have hC := gradient_sum_maximal A S h hA hh hdA
  rw [operator_sum_comm B A] at hC
  have hi := range_interior_equality A B hA.1 hd hC (gradient_lproperty S h hh)
  have hG : imOp B=gradient h '' S := gradient_operator_image S h
  have hin : gradient h '' S ⊆ interior (imOp A+imOp B) := by
    rcases hcase with hall | ⟨hopen,hzero⟩
    · obtain ⟨x,a,ha,_⟩ := gdr_minty_core A hA 1 one_pos 0
      have hsum : imOp A+imOp B=Set.univ := by
        apply Set.eq_univ_of_forall
        intro r
        apply Set.mem_add.mpr
        refine ⟨a,⟨x,ha⟩,r-a,?_,by abel⟩
        rw [hG,hall]; trivial
      rw [hsum,interior_univ]
      exact Set.subset_univ _
    · have hzeroA : (0 : H) ∈ imOp A := by
        obtain ⟨x,hx⟩ := hzero
        exact ⟨x,0,hx,by simp⟩
      apply interior_maximal _ hopen
      intro r hr
      apply Set.mem_add.mpr
      exact ⟨0,hzeroA,r,by rwa [hG],by simp⟩
  intro r hr
  have hri := hin hr
  rw [← hi] at hri
  have hm := interior_subset hri
  rwa [operator_sum_comm A B] at hm
end BregmanExistenceCodex

end

set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR BregmanPPA.Existence

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ S)
    (hcase : gradient h '' S=Set.univ ∨ (IsOpen (gradient h '' S) ∧ (0 : H) ∈ imOp T))
    (c : ℝ) (hc : 0 < c) :
    gradient h '' S ⊆ imOp (opAdd (gradOp S h) (opSmul c T)) :=
  BregmanExistenceCodex.original_image_inclusion T S h hT hh hdom hcase c hc

#print axioms solution
