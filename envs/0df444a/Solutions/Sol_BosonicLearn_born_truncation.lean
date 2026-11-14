-- Prove2me | solution 1 for BosonicLearn.born_truncation
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:08:24.0438+00:00
-- url     : https://prove2.me/submissions/245c1849-4109-4904-a48b-d6c62252f2c9

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM
import Theorems.Thm_BosonicLearn_effect_matrix_operator
import Theorems.Thm_BosonicLearn_effect_trace_pairing

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal Matrix
open Filter Topology

open BosonicLearn

noncomputable section

/-! ### Finite truncations of vectors of `ℓ²` -/

private def finVec {I : Type} [DecidableEq I] (s : Finset I) (g : I → ℂ) : Hilbert I :=
  ∑ i ∈ s, lp.single 2 i (g i)

private lemma norm_finVec_le {I : Type} [DecidableEq I] (s : Finset I) (f : Hilbert I) :
    ‖finVec s f‖ ≤ ‖f‖ := by
  have h1 := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (E := fun _ : I => ℂ) (by norm_num) f s
  have h2 := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num) f s
  have h3 : ‖finVec s f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have e : ‖finVec s f‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by simpa [finVec] using h1
    rw [e]
    simpa using h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

private lemma tendsto_finVec {I : Type} [DecidableEq I] (f : Hilbert I) :
    Tendsto (fun s : Finset I => finVec s f) atTop (𝓝 f) := by
  simpa [HasSum, finVec] using lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f

private lemma tendsto_norm_sub_finVec {I : Type} [DecidableEq I] (f : Hilbert I) :
    Tendsto (fun s : Finset I => ‖f - finVec s f‖) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := f)).sub (tendsto_finVec f)).norm
  simpa using h

private lemma norm_sub_finVec_le {I : Type} [DecidableEq I] (s : Finset I) (f : Hilbert I) :
    ‖f - finVec s f‖ ≤ 2 * ‖f‖ := by
  calc ‖f - finVec s f‖ ≤ ‖f‖ + ‖finVec s f‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := by linarith [norm_finVec_le s f]
    _ = 2 * ‖f‖ := by ring

/-- Matrix elements of a bounded operator between finitely supported vectors. -/
private lemma inner_finVec_op {I : Type} [DecidableEq I] (F : Hilbert I →L[ℂ] Hilbert I) (s : Finset I)
    (x y : I → ℂ) :
    inner ℂ (finVec s x) (F (finVec s y)) = ∑ i ∈ s, ∑ j ∈ s,
      star (x i) * inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (F (lp.single 2 j (1 : ℂ))) * y j := by
  have hs : ∀ g : I → ℂ, finVec s g = ∑ i ∈ s, g i • (lp.single 2 i (1 : ℂ) : Hilbert I) := by
    intro g
    unfold finVec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← lp.single_smul]
    simp
  rw [hs x, hs y, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.star_def]
  ring

/-! ### The operator of an effect matrix -/

/-- The hypothesis of `effect_matrix_operator`. -/
private abbrev EffB {I : Type} (E : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2

private def opOf {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) : Hilbert I →L[ℂ] Hilbert I :=
  Classical.choose (effect_matrix_operator E hE)

private lemma opOf_norm {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) : ‖opOf hE‖ ≤ 1 :=
  (Classical.choose_spec (effect_matrix_operator E hE)).1

private lemma opOf_hasSum {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (z : Hilbert I)
    (i : I) : HasSum (fun j => E i j * z j) (opOf hE z i) :=
  (Classical.choose_spec (effect_matrix_operator E hE)).2.2.1 z i

private lemma opOf_entry {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (i j : I) :
    inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (opOf hE (lp.single 2 j (1 : ℂ))) = E i j :=
  (Classical.choose_spec (effect_matrix_operator E hE)).2.2.2 i j

private lemma norm_inner_opOf_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E)
    (R L : Hilbert I) : ‖inner ℂ R (opOf hE L)‖ ≤ ‖R‖ * ‖L‖ := by
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ‖opOf hE L‖ ≤ ‖opOf hE‖ * ‖L‖ := (opOf hE).le_opNorm L
    _ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right (opOf_norm hE) (norm_nonneg _)
    _ = ‖L‖ := one_mul _

/-- Entry series of a nuclear expansion converge absolutely. -/
private lemma entry_summable {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (i j : I) :
    Summable fun a => e.left a i * star (e.right a j) := by
  refine Summable.of_norm_bounded e.summable fun a => ?_
  rw [norm_mul, norm_star]
  exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ i)
    (lp.norm_apply_le_norm (by norm_num) _ j) (norm_nonneg _) (norm_nonneg _)

/-- The truncated Born sum as a series over the nuclear expansion. -/
private lemma trunc_hasSum {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E)
    {X : Matrix I I ℂ} (e : NuclearExpansion X) (F : Finset I) :
    HasSum (fun a => inner ℂ (finVec F (e.right a)) (opOf hE (finVec F (e.left a))))
      (∑ i ∈ F, ∑ j ∈ F, E i j * X j i) := by
  have hterm : (fun a => inner ℂ (finVec F (e.right a)) (opOf hE (finVec F (e.left a)))) =
      fun a => ∑ i ∈ F, ∑ j ∈ F, E i j * (e.left a j * star (e.right a i)) := by
    funext a
    rw [inner_finVec_op]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [opOf_entry]
    ring
  rw [hterm]
  refine hasSum_sum fun i _ => hasSum_sum fun j _ => ?_
  rw [e.coefficients j i]
  exact (entry_summable e j i).hasSum.mul_left (E i j)

/-! ### Symmetry of density operators -/

private lemma dens_diag {A : Type} {X : Matrix A A ℂ} (hX : IsDensity X) (i : A) :
    (X i i).im = 0 ∧ 0 ≤ (X i i).re := by
  classical
  have h := hX.2.1 {i} (Pi.single i 1)
  simpa using h

private lemma dens_herm {A : Type} {X : Matrix A A ℂ} (hX : IsDensity X) (i j : A) :
    X j i = star (X i j) := by
  classical
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (dens_diag hX i).1).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := (dens_diag hX i).1
    have hjj := (dens_diag hX j).1
    have h1 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
    have h2 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

open scoped MatrixOrder ComplexOrder in
/-- The truncated Born sum of a positive form against a density operator is real and non-negative: the block
of the density operator is `Bᴴ B`, and the sum is a sum of quadratic forms of `E` at the rows of `B`. -/
private lemma trunc_nonneg {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (hX : IsDensity X)
    (F : Finset I) {E : Matrix I I ℂ} (hE : EffB E) :
    (∑ i ∈ F, ∑ j ∈ F, E i j * X j i).im = 0 ∧ 0 ≤ (∑ i ∈ F, ∑ j ∈ F, E i j * X j i).re := by
  let M : Matrix F F ℂ := fun a b => X a b
  have hM : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply]
      exact (dens_herm hX b a).symm
    · let z : I → ℂ := fun i => if h : i ∈ F then x ⟨i, h⟩ else 0
      have h := hX.2.1 F z
      have e : star x ⬝ᵥ M.mulVec x = ∑ i ∈ F, ∑ j ∈ F, star (z i) * X i j * z j := by
        rw [← Finset.sum_coe_sort F]
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_coe_sort F]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp [z, M, mul_assoc]
      rw [e, Complex.nonneg_iff]
      exact ⟨h.2, h.1.symm⟩
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have hMB : ∀ a b : F, X a b = ∑ c, star (B c a) * B c b := by
    intro a b
    have h := congrFun (congrFun hB a) b
    simpa [M, Matrix.mul_apply, Matrix.star_apply] using h
  let g : F → I → ℂ := fun c i => if h : i ∈ F then star (B c ⟨i, h⟩) else 0
  have key : ∑ c : F, ∑ i ∈ F, ∑ j ∈ F, star (g c i) * E i j * g c j =
      ∑ i ∈ F, ∑ j ∈ F, E i j * X j i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hMB ⟨j, hj⟩ ⟨i, hi⟩, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [g, hi, hj, dif_pos, star_star]
    ring
  rw [← key, Complex.im_sum, Complex.re_sum]
  exact ⟨Finset.sum_eq_zero fun c _ => (hE F (g c)).1, Finset.sum_nonneg fun c _ => (hE F (g c)).2.1⟩

/-! ### The statement -/

theorem solution {I : Type} [DecidableEq I] (X : Matrix I I ℂ) (hX : IsDensity X) :
    (∀ η : ℝ, 0 < η → ∃ F₀ : Finset I, ∀ F : Finset I, F₀ ⊆ F → ∀ E : Matrix I I ℂ,
      (∀ (s : Finset I) (z : I → ℂ),
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
        0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) →
      ‖(∑' i, ∑' j, E i j * X j i) - ∑ i ∈ F, ∑ j ∈ F, E i j * X j i‖ ≤ η) ∧
    (∀ (F : Finset I) (E : Matrix I I ℂ),
      (∀ (s : Finset I) (z : I → ℂ),
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
        0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) →
      (∑ i ∈ F, ∑ j ∈ F, E i j * X j i).im = 0 ∧ 0 ≤ (∑ i ∈ F, ∑ j ∈ F, E i j * X j i).re) ∧
    (∀ E : Matrix I I ℂ,
      (∀ (s : Finset I) (z : I → ℂ),
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
        0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) →
      (∑' i, ∑' j, E i j * X j i).im = 0 ∧ 0 ≤ (∑' i, ∑' j, E i j * X j i).re) := by
  obtain ⟨e⟩ := hX.1
  have part2 : ∀ (F : Finset I) (E : Matrix I I ℂ), EffB E →
      (∑ i ∈ F, ∑ j ∈ F, E i j * X j i).im = 0 ∧ 0 ≤ (∑ i ∈ F, ∑ j ∈ F, E i j * X j i).re :=
    fun F E hE => trunc_nonneg hX F hE
  have part1 : ∀ η : ℝ, 0 < η → ∃ F₀ : Finset I, ∀ F : Finset I, F₀ ⊆ F → ∀ E : Matrix I I ℂ,
      EffB E → ‖(∑' i, ∑' j, E i j * X j i) - ∑ i ∈ F, ∑ j ∈ F, E i j * X j i‖ ≤ η := by
    intro η hη
    let d : Finset I → ℕ → ℝ := fun F a =>
      ‖e.right a - finVec F (e.right a)‖ * ‖e.left a‖ +
        ‖e.right a‖ * ‖e.left a - finVec F (e.left a)‖
    have hd_nonneg : ∀ F a, 0 ≤ d F a := fun F a => by positivity
    have hd_le : ∀ F a, ‖d F a‖ ≤ 4 * (‖e.left a‖ * ‖e.right a‖) := by
      intro F a
      rw [Real.norm_of_nonneg (hd_nonneg F a)]
      have h1 := mul_le_mul_of_nonneg_right (norm_sub_finVec_le F (e.right a)) (norm_nonneg (e.left a))
      have h2 := mul_le_mul_of_nonneg_left (norm_sub_finVec_le F (e.left a)) (norm_nonneg (e.right a))
      simp only [d]
      nlinarith [norm_nonneg (e.left a), norm_nonneg (e.right a)]
    have hd_tend : ∀ a, Tendsto (fun F => d F a) atTop (𝓝 0) := by
      intro a
      have h := ((tendsto_norm_sub_finVec (e.right a)).mul_const ‖e.left a‖).add
        ((tendsto_norm_sub_finVec (e.left a)).const_mul ‖e.right a‖)
      simpa using h
    have hbound : Summable fun a => 4 * (‖e.left a‖ * ‖e.right a‖) := e.summable.mul_left 4
    have hδ : Tendsto (fun F => ∑' a, d F a) atTop (𝓝 0) := by
      have h := tendsto_tsum_of_dominated_convergence (f := d) (g := fun _ => (0 : ℝ)) hbound hd_tend
        (Eventually.of_forall hd_le)
      simpa using h
    obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.mp (hδ.eventually (Iic_mem_nhds hη))
    refine ⟨F₀, fun F hF E hE => ?_⟩
    have h1 : ∑' a, d F a ≤ η := hF₀ F hF
    have hpair := effect_trace_pairing E (opOf hE) (opOf_hasSum hE) X e
    have hS := trunc_hasSum hE e F
    rw [hpair.2.2.2, ← hS.tsum_eq, ← hpair.2.2.1.tsum_sub hS.summable]
    have hterm : ∀ a, ‖inner ℂ (e.right a) (opOf hE (e.left a)) -
        inner ℂ (finVec F (e.right a)) (opOf hE (finVec F (e.left a)))‖ ≤ d F a := by
      intro a
      have hsplit : inner ℂ (e.right a) (opOf hE (e.left a)) -
          inner ℂ (finVec F (e.right a)) (opOf hE (finVec F (e.left a))) =
          inner ℂ (e.right a - finVec F (e.right a)) (opOf hE (e.left a)) +
            inner ℂ (finVec F (e.right a)) (opOf hE (e.left a - finVec F (e.left a))) := by
        rw [inner_sub_left, map_sub, inner_sub_right]
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add (norm_inner_opOf_le hE _ _)
        ((norm_inner_opOf_le hE _ _).trans ?_))
      exact mul_le_mul_of_nonneg_right (norm_finVec_le F _) (norm_nonneg _)
    have hdsum : Summable (d F) := Summable.of_norm_bounded hbound (hd_le F)
    have hnsum : Summable fun a => ‖inner ℂ (e.right a) (opOf hE (e.left a)) -
        inner ℂ (finVec F (e.right a)) (opOf hE (finVec F (e.left a)))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdsum
    calc ‖∑' a, (inner ℂ (e.right a) (opOf hE (e.left a)) -
          inner ℂ (finVec F (e.right a)) (opOf hE (finVec F (e.left a))))‖
        ≤ ∑' a, ‖inner ℂ (e.right a) (opOf hE (e.left a)) -
          inner ℂ (finVec F (e.right a)) (opOf hE (finVec F (e.left a)))‖ :=
          norm_tsum_le_tsum_norm hnsum
      _ ≤ ∑' a, d F a := Summable.tsum_le_tsum hterm hnsum hdsum
      _ ≤ η := h1
  refine ⟨part1, part2, fun E hE => ?_⟩
  constructor
  · by_contra h
    have hpos : 0 < |(∑' i, ∑' j, E i j * X j i).im| := abs_pos.mpr h
    obtain ⟨F₀, hF₀⟩ := part1 (|(∑' i, ∑' j, E i j * X j i).im| / 2) (by positivity)
    have h1 := hF₀ F₀ subset_rfl E hE
    have h2 := (part2 F₀ E hE).1
    have h3 := Complex.abs_im_le_norm ((∑' i, ∑' j, E i j * X j i) - ∑ i ∈ F₀, ∑ j ∈ F₀, E i j * X j i)
    rw [Complex.sub_im, h2, sub_zero] at h3
    linarith
  · by_contra h
    rw [not_le] at h
    obtain ⟨F₀, hF₀⟩ := part1 (-(∑' i, ∑' j, E i j * X j i).re / 2) (by linarith)
    have h1 := hF₀ F₀ subset_rfl E hE
    have h2 := (part2 F₀ E hE).2
    have h3 := Complex.abs_re_le_norm ((∑' i, ∑' j, E i j * X j i) - ∑ i ∈ F₀, ∑ j ∈ F₀, E i j * X j i)
    rw [Complex.sub_re] at h3
    have h4 := neg_abs_le ((∑' i, ∑' j, E i j * X j i).re - (∑ i ∈ F₀, ∑ j ∈ F₀, E i j * X j i).re)
    linarith
