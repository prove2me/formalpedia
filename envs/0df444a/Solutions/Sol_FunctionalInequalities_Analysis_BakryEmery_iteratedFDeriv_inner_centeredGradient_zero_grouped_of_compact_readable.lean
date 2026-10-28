-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:27.402924+00:00
-- url     : https://prove2.me/submissions/dc39e516-1679-4f45-9a6d-ee4a5ee2b288

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Leibniz
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_cumulantVector_single_ringInverse_cumulantVector_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_centeredGradient_zero_of_compact_readable
import Theorems.Thm_FunctionalInequalities_Analysis_selected_mask_partition_readable
import Theorems.Thm_FunctionalInequalities_Analysis_sum_filter_eq_two_mul_sum_filter_of_compl_invariant_readable

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The covariance operator is self-adjoint. -/
theorem FunctionalInequalities.Covariance.operator_isSelfAdjoint (μ : Measure E) : IsSelfAdjoint (Covariance.operator μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪Covariance.operator μ x, y⟫ = ⟪x, Covariance.operator μ y⟫
  calc
    ⟪Covariance.operator μ x, y⟫ = covarianceBilin μ x y := Covariance.operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = ⟪Covariance.operator μ y, x⟫ := (Covariance.operator_inner μ y x).symm
    _ = ⟪x, Covariance.operator μ y⟫ := real_inner_comm _ _
end
end

section
noncomputable section
open scoped ContDiff
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem FunctionalInequalities.Analysis.directional_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) :
    ContDiff ℝ ∞ (directional hs f) := by
  induction hs with
  | nil => exact hf
  | cons h hs IH =>
    exact (ContinuousLinearMap.apply ℝ F h).contDiff.comp (IH.fderiv_right (by simp))
private theorem FunctionalInequalities.Analysis.directional_two {f : E → F} (hf : ContDiff ℝ ∞ f) (v w x : E) :
    directional [v, w] f x = fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hDf.differentiable (by simp) x) (differentiableAt_const w)]
  simp
/-- Adjacent directional derivatives commute by genuine real C² symmetry. -/
theorem FunctionalInequalities.Analysis.directional_swap {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) (v w : E) :
    directional (v :: w :: hs) f = directional (w :: v :: hs) f := by
  funext x
  have hg := directional_contDiff hf hs
  have he (u t : E) : directional (u :: t :: hs) f x = directional [u,t] (directional hs f) x := rfl
  rw [he, he, directional_two hg, directional_two hg]
  exact hg.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) v w
/-- Full permutation symmetry follows from adjacent swaps; no tensor symmetry is a premise. -/
theorem FunctionalInequalities.Analysis.directional_perm {f : E → F} (hf : ContDiff ℝ ∞ f) {hs ks : List E}
    (h : hs.Perm ks) : directional hs f = directional ks f := by
  induction h with
  | nil => rfl
  | cons v h IH =>
    change (fun x => fderiv ℝ (directional _ f) x v) = (fun x => fderiv ℝ (directional _ f) x v)
    rw [IH]
  | swap v w hs => exact directional_swap hf hs w v
  | trans h1 h2 IH1 IH2 => exact IH1.trans IH2
/-- The directional list convention is exactly the raw iterated Fréchet derivative. -/
theorem FunctionalInequalities.Analysis.directional_ofFn {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) f x = iteratedFDeriv ℝ m f x h := by
  induction m generalizing x with
  | zero => simp [directional]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) f) x (h 0) = _
    have he : directional (List.ofFn (Fin.tail h)) f =
        fun y => iteratedFDeriv ℝ m f y (Fin.tail h) := funext (fun y => IH (Fin.tail h) y)
    rw [he]
    exact ((hf.differentiable_iteratedFDeriv (m := m)
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) x).iteratedFDeriv_succ_apply_left').symm
/-- Raw real C∞ iterated derivatives are symmetric under every slot permutation. -/
theorem FunctionalInequalities.Analysis.iteratedFDeriv_perm {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (h : Fin m → E) (σ : Equiv.Perm (Fin m)) (x : E) :
    iteratedFDeriv ℝ m f x (h ∘ σ) = iteratedFDeriv ℝ m f x h := by
  rw [← directional_ofFn hf, ← directional_ofFn hf]
  exact congrFun (directional_perm hf (σ.ofFn_comp_perm h)) x
end
end
end

section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CompactSupport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
/-- A law with compact support has every exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp (μ : Measure F) [IsFiniteMeasure μ]
    (hc : IsCompact μ.support) (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖)) μ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : F)
  refine (integrable_const (Real.exp (|r| * max R 0))).mono' (by fun_prop) ?_
  filter_upwards [μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r * ‖x‖ ≤ |r| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |r| * max R 0 := by
      gcongr
      exact (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)
end CompactSupport
section CumulantSymmetry
/-- The cumulant tensors of a compactly supported law are symmetric: `κ_m(h ∘ σ) = κ_m(h)` for every permutation `σ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_comp_perm_of_compact (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (h : Fin m → E) :
    cumulant (μ : Measure E) m (h ∘ σ) = cumulant (μ : Measure E) m h := by
    have hΛ : ContDiff ℝ ∞ (logLaplace (μ : Measure E)) :=
      contDiff_logLaplace _ (compact_support_integrable_exp _ hc)
    simp only [cumulant]
    exact iteratedFDeriv_perm hΛ m h σ 0
end CumulantSymmetry
end
end

section
noncomputable section
open scoped ContDiff
section
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The mask selector returns the empty list exactly for the all-`false` mask. -/
theorem FunctionalInequalities.Analysis.selected_eq_nil_iff {m : ℕ} (h : Fin m → E) (q : Fin m → Bool) :
    selected h q = [] ↔ ∀ i, q i = false := by
    induction m with
    | zero =>
        simp [selected]
    | succ m ih =>
        cases hq0 : q 0 with
        | false =>
            simp [selected, hq0, ih (Fin.tail h) (Fin.tail q),
              Fin.forall_fin_succ, Fin.tail]
        | true =>
            simp [selected, hq0, Fin.forall_fin_succ]
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Exact deterministic grouping of BKL arXiv:2610.05474v1, (72)–(74), at a fixed law: the `2m`
singleton/complement allocations give `2m * kappa_m`, and all middle allocations pair to twice the sum over the
middle masks containing the slot `i0` (72). It assumes only compact support and invertibility of the actual
covariance, for every `m ≥ 3`; it contains no stochastic process, Itô formula or cumulant evolution conclusion.
-/
theorem solution
    (mu : ProbabilityMeasure E)
    (hc : IsCompact (mu : Measure E).support)
    (hA : IsUnit (FunctionalInequalities.Covariance.operator (mu : Measure E)))
    {m : ℕ} (hm : 3 ≤ m) (h : Fin m → E) (i0 : Fin m) :
    iteratedFDeriv ℝ m (fun z : E =>
        ⟪gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) z - gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) 0,
          Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E))
            (gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) z -
              gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) 0)⟫) 0 h =
      (2 * (m : ℝ)) * FunctionalInequalities.Analysis.BakryEmery.cumulant (mu : Measure E) m h +
        2 * ∑ q ∈ Finset.univ.filter (fun q : Fin m → Bool =>
          q i0 = true ∧
          2 ≤ (FunctionalInequalities.Analysis.selected h q).length ∧
          2 ≤ (FunctionalInequalities.Analysis.selected h (fun i => !(q i))).length),
          ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (mu : Measure E) (FunctionalInequalities.Analysis.selected h q),
            Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E))
              (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (mu : Measure E)
                (FunctionalInequalities.Analysis.selected h (fun i => !(q i))))⟫ := by
  classical
  let F : (Fin m → Bool) → ℝ := fun q =>
    ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (mu : Measure E) (FunctionalInequalities.Analysis.selected h q),
      Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E))
        (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (mu : Measure E)
          (FunctionalInequalities.Analysis.selected h (fun i => !(q i))))⟫
  let l : (Fin m → Bool) → ℕ := fun q => (FunctionalInequalities.Analysis.selected h q).length
  let r : (Fin m → Bool) → ℕ :=
    fun q => (FunctionalInequalities.Analysis.selected h (fun i => !(q i))).length
  let U := Finset.univ.filter
    (fun q : Fin m → Bool => 1 ≤ l q ∧ 1 ≤ r q)
  let A := Finset.univ.filter (fun q : Fin m → Bool => l q = 1)
  let B := Finset.univ.filter (fun q : Fin m → Bool => r q = 1)
  let C := fun q : Fin m → Bool => 2 ≤ l q ∧ 2 ≤ r q
  let M := Finset.univ.filter C
  let T := Finset.univ.filter
    (fun q : Fin m → Bool => q i0 = true ∧ C q)

  have hlen (q : Fin m → Bool) : l q + r q = m := by
    exact (FunctionalInequalities.Analysis.selected_mask_partition_readable h q).1

  have hinv (x y : E) :
      ⟪x, Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E)) y⟫ =
        ⟪y, Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E)) x⟫ := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    have hs := (FunctionalInequalities.Covariance.operator_isSelfAdjoint (mu : Measure E)).ringInverse
    have hsym :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs
    calc
      ⟪x, Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E)) y⟫ =
          ⟪Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E)) x, y⟫ :=
        (hsym x y).symm
      _ = ⟪y, Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E)) x⟫ :=
        real_inner_comm _ _

  have hFcomp (q : Fin m → Bool) :
      F (fun i => !(q i)) = F q := by
    dsimp [F]
    simp only [Bool.not_not]
    exact
      (hinv
        (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (mu : Measure E) (FunctionalInequalities.Analysis.selected h q))
        (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (mu : Measure E)
          (FunctionalInequalities.Analysis.selected h (fun i => !(q i))))).symm

  have hpos (q : Fin m → Bool) :
      1 ≤ l q ↔ ∃ i : Fin m, q i = true := by
    constructor
    · intro hq
      by_contra hno
      push Not at hno
      have hall : ∀ i : Fin m, q i = false := by
        intro i
        cases hi : q i with
        | false => rfl
        | true => exact False.elim (hno i hi)
      have he : FunctionalInequalities.Analysis.selected h q = [] :=
        (FunctionalInequalities.Analysis.selected_eq_nil_iff h q).2 hall
      have hz : (FunctionalInequalities.Analysis.selected h q).length = 0 := by
        simp [he]
      change 1 ≤ (FunctionalInequalities.Analysis.selected h q).length at hq
      omega
    · rintro ⟨i, hi⟩
      have hz : (FunctionalInequalities.Analysis.selected h q).length ≠ 0 := by
        intro hz
        have he : FunctionalInequalities.Analysis.selected h q = [] :=
          List.length_eq_zero_iff.mp hz
        have hall := (FunctionalInequalities.Analysis.selected_eq_nil_iff h q).mp he
        simpa [hi] using hall i
      change 1 ≤ (FunctionalInequalities.Analysis.selected h q).length
      omega

  have hposFalse (q : Fin m → Bool) :
      1 ≤ r q ↔ ∃ i : Fin m, q i = false := by
    constructor
    · intro hq
      have ht :
          ∃ i : Fin m, (fun j => !(q j)) i = true :=
        (hpos (fun j => !(q j))).1 (by simpa [r] using hq)
      obtain ⟨i, hi⟩ := ht
      cases hqi : q i with
      | false => exact ⟨i, hqi⟩
      | true => simp [hqi] at hi
    · rintro ⟨i, hi⟩
      apply (hpos (fun j => !(q j))).2
      refine ⟨i, ?_⟩
      simp [hi]

  have hfilter :
      Finset.univ.filter
          (fun q : Fin m → Bool =>
            (∃ i, q i = true) ∧ ∃ i, q i = false) = U := by
    ext q
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ht, hf⟩
      exact ⟨(hpos q).2 ht, (hposFalse q).2 hf⟩
    · intro hq
      exact ⟨(hpos q).1 hq.1, (hposFalse q).1 hq.2⟩

  have bridge : ∀ {k : ℕ} (f g : Fin k → E),
      (List.ofFn f).Perm (List.ofFn g) →
        ∃ σ : Equiv.Perm (Fin k), g ∘ σ = f := by
    intro k f g hp
    have hm : (Finset.univ.val.map f : Multiset E) =
        Finset.univ.val.map g := by
      rw [Fin.univ_val_map, Fin.univ_val_map]
      exact Multiset.coe_eq_coe.mpr hp
    have hcard : ∀ a, Fintype.card {i // f i = a} =
        Fintype.card {i // g i = a} := by
      intro a
      have hc := congrArg (Multiset.count a) hm
      rw [Multiset.count_map, Multiset.count_map] at hc
      simp only [Fintype.card_subtype]
      simpa [Finset.card, Finset.filter_val, eq_comm] using hc
    exact
      ⟨Equiv.ofFiberEquiv (fun a =>
          Fintype.equivOfCardEq (hcard a)),
        funext fun j => Equiv.ofFiberEquiv_map _ j⟩

  have hsingleTerm (i : Fin m) :
      F (fun j => decide (j = i)) =
        FunctionalInequalities.Analysis.BakryEmery.cumulant (mu : Measure E) m h := by
    dsimp [F]
    obtain ⟨hlen', hperm, hsing, -⟩ :=
      FunctionalInequalities.Analysis.selected_mask_partition_readable h (fun j => decide (j = i))
    set rest := FunctionalInequalities.Analysis.selected h (fun j => !decide (j = i)) with hrest
    rw [hsing i] at hlen' hperm ⊢
    rw [FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector_readable
      mu hc hA rest (h i)]
    have hl : rest.length + 1 = m := by
      simpa [Nat.add_comm] using hlen'
    have key : ∀ (k : ℕ) (hk : k = m) (v : Fin k → E),
        (List.ofFn v).Perm (List.ofFn h) →
          FunctionalInequalities.Analysis.BakryEmery.cumulant (mu : Measure E) k v =
            FunctionalInequalities.Analysis.BakryEmery.cumulant (mu : Measure E) m h := by
      rintro k rfl v hv
      obtain ⟨σ, hσ⟩ := bridge v h hv
      rw [← hσ, FunctionalInequalities.Analysis.BakryEmery.cumulant_comp_perm_of_compact mu hc]
    apply key _ hl
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
      List.ofFn_get]
    exact (List.perm_append_comm).trans hperm

  have hraw :
      iteratedFDeriv ℝ m (fun z : E =>
          ⟪gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) z -
              gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) 0,
            Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E))
              (gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) z -
                gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) 0)⟫) 0 h =
        ∑ q ∈ U, F q := by
    calc
      iteratedFDeriv ℝ m (fun z : E =>
          ⟪gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) z -
              gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) 0,
            Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E))
              (gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) z -
                gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (mu : Measure E)) 0)⟫) 0 h =
          ∑ q ∈ Finset.univ.filter
            (fun q : Fin m → Bool =>
              (∃ i, q i = true) ∧ ∃ i, q i = false), F q := by
        simpa [F] using
          (FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact_readable
            mu hc (Ring.inverse (FunctionalInequalities.Covariance.operator (mu : Measure E))) m h)
      _ = ∑ q ∈ U, F q := by
        rw [hfilter]

  have hUA : U.filter (fun q => l q = 1) = A := by
    ext q
    simp only [U, A, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := hlen q
    omega

  have hUB :
      (U.filter (fun q => l q ≠ 1)).filter (fun q => r q = 1) = B := by
    ext q
    simp only [U, B, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := hlen q
    omega

  have hUM :
      (U.filter (fun q => l q ≠ 1)).filter (fun q => r q ≠ 1) = M := by
    ext q
    simp only [U, M, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := hlen q
    omega

  have hdecomp :
      (∑ q ∈ U, F q) =
        (∑ q ∈ A, F q) + (∑ q ∈ B, F q) + ∑ q ∈ M, F q := by
    have hs₁ :=
      Finset.sum_filter_add_sum_filter_not U (fun q => l q = 1) F
    have hs₂ :=
      Finset.sum_filter_add_sum_filter_not
        (U.filter (fun q => l q ≠ 1)) (fun q => r q = 1) F
    calc
      (∑ q ∈ U, F q) =
          (∑ q ∈ U.filter (fun q => l q = 1), F q) +
            ∑ q ∈ U.filter (fun q => l q ≠ 1), F q := hs₁.symm
      _ =
          (∑ q ∈ A, F q) +
            ((∑ q ∈
                (U.filter (fun q => l q ≠ 1)).filter
                  (fun q => r q = 1), F q) +
              ∑ q ∈
                (U.filter (fun q => l q ≠ 1)).filter
                  (fun q => r q ≠ 1), F q) := by
        rw [hUA, ← hs₂]
      _ = (∑ q ∈ A, F q) + (∑ q ∈ B, F q) + ∑ q ∈ M, F q := by
        rw [hUB, hUM]
        ring

  have hAsingle :
      (∑ q ∈ A, F q) =
        ∑ i : Fin m, F (fun j => decide (j = i)) := by
    symm
    refine Finset.sum_bij
      (fun i _ => fun j => decide (j = i)) ?_ ?_ ?_ ?_
    · intro i _
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      change (FunctionalInequalities.Analysis.selected h (fun j => decide (j = i))).length = 1
      rw [(FunctionalInequalities.Analysis.selected_mask_partition_readable h
        (fun j => decide (j = i))).2.2.1 i]
      rfl
    · intro a _ b _ hab
      simpa using congrFun hab a
    · intro q hq
      obtain ⟨i, rfl⟩ :=
        (FunctionalInequalities.Analysis.selected_mask_partition_readable h q).2.2.2
          (Finset.mem_filter.mp hq).2
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · intro i _
      rfl

  have hAsum :
      (∑ q ∈ A, F q) =
        (m : ℝ) * FunctionalInequalities.Analysis.BakryEmery.cumulant (mu : Measure E) m h := by
    calc
      (∑ q ∈ A, F q) =
          ∑ i : Fin m, F (fun j => decide (j = i)) := hAsingle
      _ = ∑ _i : Fin m, FunctionalInequalities.Analysis.BakryEmery.cumulant (mu : Measure E) m h := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsingleTerm i
      _ = (m : ℝ) * FunctionalInequalities.Analysis.BakryEmery.cumulant (mu : Measure E) m h := by
        simp

  have hcomp_inj :
      ∀ {a b : Fin m → Bool},
        (fun i => !(a i)) = (fun i => !(b i)) → a = b := by
    intro a b hab
    have hinvol :
        Function.Involutive
          (fun q : Fin m → Bool => fun i => !(q i)) := by
      intro q
      funext i
      simp only [Bool.not_not]
    exact hinvol.injective hab

  have hBsum :
      (∑ q ∈ B, F q) = (∑ q ∈ A, F q) := by
    refine Finset.sum_bij
      (fun q _ => fun i => !(q i)) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [l, r] using (Finset.mem_filter.mp hq).2
    · intro a _ b _ hab
      exact hcomp_inj hab
    · intro q hq
      refine ⟨fun i => !(q i), ?_, ?_⟩
      · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [l, r] using (Finset.mem_filter.mp hq).2
      · funext i
        simp
    · intro q hq
      exact (hFcomp q).symm

  have hCcomp (q : Fin m → Bool) :
      C (fun i => !(q i)) ↔ C q := by
    simp [C, l, r, and_comm]

  have hMsum :
      (∑ q ∈ M, F q) =
        2 * ∑ q ∈ T, F q := by
    exact
      FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant_readable
        C hCcomp F hFcomp i0

  rw [hraw, hdecomp]
  simp only [hBsum, hAsum, hMsum]
  dsimp [T, F, C, l, r]
  ring
