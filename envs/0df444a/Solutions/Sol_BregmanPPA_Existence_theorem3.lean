-- Prove2me | solution 1 for BregmanPPA.Existence.theorem3
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T16:00:30.661308+00:00
-- url     : https://prove2.me/submissions/350ea623-bdd0-416c-b037-24d86c36c961

import Definitions.Def_BregmanPPA_Existence_LProperty
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

set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR BregmanPPA.Existence
open scoped Pointwise

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (A B : H → Set H)
    (hA : IsMonotoneOp A) (hB : IsMonotoneOp B)
    (ha : dom A ⊆ dom B) (hb : IsMaximalMonotone (opAdd A B))
    (hc : HasLProperty B) :
    interior (imOp (opAdd A B)) = interior (imOp A+imOp B) ∧
    closure (imOp (opAdd A B)) = closure (imOp A+imOp B) := by
  exact ⟨BregmanExistenceCodex.range_interior_equality A B hA ha hb hc,
    BregmanExistenceCodex.range_closure_equality A B hA ha hb hc⟩

#print axioms solution
