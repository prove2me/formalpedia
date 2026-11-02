-- Prove2me | solution 1 for GenPayoffSG.Solvable.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:41:06.150364+00:00
-- url     : https://prove2.me/submissions/3bb5a06b-9146-46e1-8bff-7578646c87b2

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_GenPayoffSG_Solvable_OneShot

open MeasureTheory ProbabilityTheory Filter Topology GenPayoffSG.Solvable

set_option linter.unusedSectionVars false

namespace GPSGEq15

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-! ### One-shot facts -/

lemma toReal_update (x : ∀ j, PMF (A j)) (i : I) (y : PMF (A i)) :
    (fun j b => (Function.update x i y j b).toReal) =
      Function.update (fun j b => (x j b).toReal) i (fun b => (y b).toReal) := by
  funext j b
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

lemma oneShotPayoff_eq_expected (G : Game I S A) (D : I → HistFun I S A) {n : ℕ}
    (h : Hist I S A n) (x : ∀ j, PMF (A j)) (i : I) :
    oneShotPayoff G (D i) h x =
      AGT.expectedPayoff (fun j a => oneShotPayoffPure G (D j) h a)
        (fun j b => (x j b).toReal) i := by
  unfold oneShotPayoff AGT.expectedPayoff AGT.profileProb
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma oneShotPayoff_bdd (G : Game I S A) (Di : HistFun I S A) {n : ℕ}
    (h : Hist I S A n) (x : ∀ j, PMF (A j)) :
    |oneShotPayoff G Di h x| ≤ ∑ a : ∀ j, A j, |oneShotPayoffPure G Di h a| := by
  unfold oneShotPayoff
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  have h1 : |∏ j, (x j (a j)).toReal| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun j _ => ?_
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one (x j) (a j))
  calc |oneShotPayoffPure G Di h a| * |∏ j, (x j (a j)).toReal|
      ≤ |oneShotPayoffPure G Di h a| * 1 := by gcongr
    _ = _ := mul_one _

lemma minmax_le_of_eq (G : Game I S A) (D : I → HistFun I S A) {n : ℕ}
    (h : Hist I S A n) (x : ∀ j, PMF (A j)) (hx : IsOneShotEquilibrium G D h x) (i : I) :
    oneShotMinmax G i (D i) h ≤ oneShotPayoff G (D i) h x := by
  set M := ∑ a : ∀ j, A j, |oneShotPayoffPure G (D i) h a|
  have hb : ∀ z, |oneShotPayoff G (D i) h z| ≤ M := fun z => oneShotPayoff_bdd G (D i) h z
  have hle : ∀ y : PMF (A i), oneShotPayoff G (D i) h (Function.update x i y) ≤
      oneShotPayoff G (D i) h x := by
    intro y
    rw [oneShotPayoff_eq_expected G D h _ i, oneShotPayoff_eq_expected G D h _ i,
      toReal_update]
    refine hx.2 i _ ⟨fun b => ENNReal.toReal_nonneg, ?_⟩
    rw [← ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top y b)]
    have := PMF.tsum_coe y
    rw [tsum_fintype] at this
    simp [this]
  unfold oneShotMinmax
  have hbdd : BddBelow (Set.range fun z : (∀ j, PMF (A j)) =>
      ⨆ y : PMF (A i), oneShotPayoff G (D i) h (Function.update z i y)) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨z, rfl⟩
    have h0 := hb (Function.update z i (PMF.pure (Classical.arbitrary (A i))))
    have hbu : BddAbove (Set.range fun y : PMF (A i) =>
        oneShotPayoff G (D i) h (Function.update z i y)) :=
      ⟨M, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (hb _)⟩
    exact (neg_le_of_abs_le h0).trans (le_ciSup hbu _)
  refine (ciInf_le hbdd x).trans ?_
  exact ciSup_le hle

/-! ### Histories -/

lemma histCoord_extend_le {n : ℕ} (h : Hist I S A n) (a : ∀ i, A i) (s : S) (k : ℕ)
    (hk : k ≤ n) : histCoord (GenPayoffSG.Solvable.extend h a s) k (hk.trans n.le_succ) = histCoord h k hk := by
  unfold histCoord GenPayoffSG.Solvable.extend
  simp [hk]

lemma histCoord_extend_last {n : ℕ} (h : Hist I S A n) (a : ∀ i, A i) (s : S) :
    histCoord (GenPayoffSG.Solvable.extend h a s) (n + 1) le_rfl = ((a, s) : Coord I S A (n + 1)) := by
  unfold histCoord GenPayoffSG.Solvable.extend
  simp
  rfl

lemma feasible_extend (G : Game I S A) {n : ℕ} (h : Hist I S A n) (hh : Feasible G h)
    (a : ∀ i, A i) (s : S) (hp : 0 < G.p (lastState h) a s) : Feasible G (GenPayoffSG.Solvable.extend h a s) := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
  · have e1 := histCoord_extend_le h a s k hk'.le
    have e2 := histCoord_extend_le h a s (k + 1) hk'
    rw [e1, e2]
    exact hh k hk'
  · have e1 := histCoord_extend_le h a s k le_rfl
    have e2 := histCoord_extend_last h a s
    rw [e1, e2]
    exact hp

lemma frestrictLe_succ (y : Run I S A) (n : ℕ) :
    Preorder.frestrictLe (n + 1) y =
      GenPayoffSG.Solvable.extend (Preorder.frestrictLe n y) (coordAction (y (n + 1))) (coordState (n + 1) (y (n + 1))) := by
  funext ⟨k, hk⟩
  unfold GenPayoffSG.Solvable.extend
  by_cases hkn : k ≤ n
  · simp [hkn]
  · have : k = n + 1 := by have := Finset.mem_Iic.1 hk; omega
    subst this
    simp [hkn]
    rfl

/-! ### The one-step integral -/

lemma stepPMF_apply (G : Game I S A) (σ : Profile G) (n : ℕ) (h : Hist I S A n)
    (a : ∀ i, A i) (s : S) :
    stepPMF G σ n h ((a, s) : Coord I S A (n + 1)) = actionPMF G σ n h a * G.p (lastState h) a s := by
  change ((actionPMF G σ n h).bind (fun a => (G.p (lastState h) a).map
    (fun s' => ((a, s') : (∀ i, A i) × S)))) ((a, s) : (∀ i, A i) × S) = _
  rw [PMF.bind_apply, tsum_eq_single a]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single s]
    · simp
    · intro s' hs'
      have : ¬ ((a, s) : (∀ i, A i) × S) = (a, s') := by
        intro he; exact hs' (Prod.ext_iff.1 he).2.symm
      simp [this]
  · intro a' ha'
    rw [PMF.map_apply]
    have : ∀ s', ¬ ((a, s) : (∀ i, A i) × S) = (a', s') := by
      intro s' he; exact ha' (Prod.ext_iff.1 he).1.symm
    simp [this]

lemma integral_step (G : Game I S A) (σ : Profile G) (n : ℕ) (h : Hist I S A n)
    (F : Hist I S A (n + 1) → ℝ) (C : ℝ) (hF : ∀ h', |F h'| ≤ C) :
    ∫ y, F (Preorder.frestrictLe (n + 1) y) ∂(Kernel.traj (stepKernel G σ) n h) =
      ∑ a : ∀ j, A j, (∏ j, (σ j n h (a j)).toReal) *
        ∑' s, (G.p (lastState h) a s).toReal * F (GenPayoffSG.Solvable.extend h a s) := by
  let φ : Run I S A → Hist I S A n × Coord I S A (n + 1) :=
    fun x => (Preorder.frestrictLe n x, x (n + 1))
  let Ψ : Hist I S A n × Coord I S A (n + 1) → ℝ :=
    fun p => F (GenPayoffSG.Solvable.extend p.1 (coordAction p.2) (coordState (n + 1) p.2))
  have hφ : Measurable φ := by fun_prop
  have hΨ : Measurable Ψ := measurable_of_countable Ψ
  have hcomp : ∫ y, F (Preorder.frestrictLe (n + 1) y) ∂(Kernel.traj (stepKernel G σ) n h) =
      ∫ y, Ψ (φ y) ∂(Kernel.traj (stepKernel G σ) n h) := by
    congr 1
    funext y
    simp only [Ψ, φ]
    rw [frestrictLe_succ]
  have hmap : (Kernel.traj (stepKernel G σ) n h).map φ =
      Measure.dirac h ⊗ₘ (stepKernel G σ n) := by
    have := (Kernel.partialTraj_compProd_eq_map_traj (κ := stepKernel G σ) (le_refl n) (x₀ := h))
    rw [← this, Kernel.partialTraj_self, Kernel.id_apply]
  have hΨb : ∀ p, ‖Ψ p‖ ≤ C := fun p => by simpa [Real.norm_eq_abs] using hF _
  rw [hcomp, ← integral_map hφ.aemeasurable hΨ.aestronglyMeasurable, hmap,
    Measure.integral_compProd (Integrable.of_bound hΨ.aestronglyMeasurable C (ae_of_all _ hΨb)),
    integral_dirac]
  change ∫ c, Ψ (h, c) ∂(stepPMF G σ n h).toMeasure = _
  have hint : Integrable (fun c => Ψ (h, c)) (stepPMF G σ n h).toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C (ae_of_all _ fun c => hΨb _)
  rw [PMF.integral_eq_tsum _ _ hint]
  change ∑' c : (∀ i, A i) × S, (stepPMF G σ n h c).toReal • Ψ (h, c) = _
  have hsum : Summable (fun c : (∀ i, A i) × S => (stepPMF G σ n h c).toReal • Ψ (h, c)) := by
    refine Summable.of_norm_bounded (g := fun c => C * (stepPMF G σ n h c).toReal) ?_ ?_
    · exact (ENNReal.summable_toReal (ne_of_eq_of_ne (PMF.tsum_coe (stepPMF G σ n h)) ENNReal.one_ne_top)).mul_left C
    · intro c
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, mul_comm]
      exact mul_le_mul_of_nonneg_right (hΨb _) ENNReal.toReal_nonneg
  rw [hsum.tsum_prod' (fun a => hsum.prod_factor a), tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun s => ?_
  rw [smul_eq_mul, stepPMF_apply, ENNReal.toReal_mul]
  simp only [actionPMF, PMF.ofFintype_apply, ENNReal.toReal_prod, Ψ]
  ring_nf
  rfl

/-! ### Almost-sure feasibility -/

lemma stepPMF_bad_zero (G : Game I S A) (σ : Profile G) (k : ℕ) (h : Hist I S A k) :
    (stepPMF G σ k h).toMeasure
      {c | G.p (lastState h) (coordAction c) (coordState (k + 1) c) = 0} = 0 := by
  rw [(stepPMF G σ k h).toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete]
  rw [Set.disjoint_left]
  intro c hc hbad
  unfold stepPMF at hc
  rw [PMF.mem_support_bind_iff] at hc
  obtain ⟨a, _, hc⟩ := hc
  rw [PMF.mem_support_map_iff] at hc
  obtain ⟨s', hs', rfl⟩ := hc
  exact hs' hbad

lemma ae_trans_pos (G : Game I S A) (σ : Profile G) (s : S) (k : ℕ) :
    ∀ᵐ r ∂(playMeasure G σ 0 (initHist s)),
      0 < G.p (coordState k (r k)) (coordAction (r (k + 1))) (coordState (k + 1) (r (k + 1))) := by
  set μ := playMeasure G σ 0 (initHist s)
  let φ : Run I S A → Hist I S A k × Coord I S A (k + 1) :=
    fun x => (Preorder.frestrictLe k x, x (k + 1))
  let E : Set (Hist I S A k × Coord I S A (k + 1)) :=
    {p | G.p (lastState p.1) (coordAction p.2) (coordState (k + 1) p.2) = 0}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hφ : Measurable φ := by fun_prop
  have hmap : μ.map φ = (Kernel.partialTraj (stepKernel G σ) 0 k (initHist s)) ⊗ₘ
      (stepKernel G σ k) :=
    (Kernel.partialTraj_compProd_eq_map_traj (κ := stepKernel G σ) (Nat.zero_le k)).symm
  have h0 : μ (φ ⁻¹' E) = 0 := by
    rw [← Measure.map_apply hφ hE, hmap, Measure.compProd_apply hE]
    have : ∀ h : Hist I S A k, stepKernel G σ k h (Prod.mk h ⁻¹' E) = 0 := fun h =>
      stepPMF_bad_zero G σ k h
    simp [this]
  rw [ae_iff]
  refine le_antisymm (le_of_le_of_eq (measure_mono ?_) h0) zero_le
  intro r hr
  simp only [Set.mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] at hr
  exact hr

lemma ae_feasible (G : Game I S A) (σ : Profile G) (s : S) :
    ∀ᵐ r ∂(playMeasure G σ 0 (initHist s)), ∀ n, Feasible G (Preorder.frestrictLe n r) := by
  have := ae_all_iff.2 (ae_trans_pos G σ s)
  filter_upwards [this] with r hr n k hk
  exact hr k

lemma stronglyMeasurable_piLE (n : ℕ) (g : Hist I S A n → ℝ) :
    StronglyMeasurable[Filtration.piLE n] (fun r : Run I S A => g (Preorder.frestrictLe n r)) := by
  apply Measurable.stronglyMeasurable
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_countable g).comp (comap_measurable _)

end GPSGEq15

open GPSGEq15

theorem solution {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
  (G : Game I S A) (δ : ℝ) (hδ : 0 < δ) (D : I → HistFun I S A)
    (hD : ∀ i, IsMartinFunction G δ i (D i))
    (x : (n : ℕ) → Hist I S A n → ∀ j, PMF (A j))
    (hx : ∀ n (h : Hist I S A n), Feasible G h → IsOneShotEquilibrium G D h (x n h))
    (s : S) (i : I) :
    Submartingale (fun n r => D i n (Preorder.frestrictLe n r)) Filtration.piLE
      (playMeasure G (fun j n h => x n h j) 0 (initHist s)) := by
  set σ : Profile G := fun j n h => x n h j with hσ
  set μ := playMeasure G σ 0 (initHist s) with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; unfold playMeasure; infer_instance
  obtain ⟨⟨C, hC⟩, _, h2, _⟩ := hD i
  -- truncated version of `D i`, bounded everywhere and equal to `D i` on feasible histories
  let Dt : HistFun I S A := fun m h => max (-C) (min C (D i m h))
  have hDt_eq : ∀ m (h : Hist I S A m), Feasible G h → Dt m h = D i m h := by
    intro m h hh
    have := abs_le.1 (hC m h hh)
    simp only [Dt]
    rw [min_eq_right this.2, max_eq_right this.1]
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 (initHist s) (fun k hk => absurd hk (Nat.not_lt_zero k)))
  have hDt_bd : ∀ m (h : Hist I S A m), |Dt m h| ≤ C := by
    intro m h
    simp only [Dt]
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hfeas := ae_feasible G σ s
  -- the process equals the truncated process a.s.
  have hYeq : ∀ n, (fun r => D i n (Preorder.frestrictLe n r)) =ᵐ[μ]
      (fun r => Dt n (Preorder.frestrictLe n r)) := by
    intro n
    filter_upwards [hfeas] with r hr
    exact (hDt_eq n _ (hr n)).symm
  have hintt : ∀ n, Integrable (fun r => Dt n (Preorder.frestrictLe n r)) μ := by
    intro n
    refine Integrable.of_bound ((measurable_of_countable (Dt n)).comp
      (Preorder.measurable_frestrictLe n)).aestronglyMeasurable C (ae_of_all _ fun r => ?_)
    simpa [Real.norm_eq_abs] using hDt_bd n _
  have hint : ∀ n, Integrable (fun r => D i n (Preorder.frestrictLe n r)) μ :=
    fun n => (hintt n).congr (hYeq n).symm
  refine submartingale_nat (fun n => stronglyMeasurable_piLE n (D i n)) hint fun n => ?_
  have hce : μ[fun r => D i (n + 1) (Preorder.frestrictLe (n + 1) r) | Filtration.piLE n] =ᵐ[μ]
      fun r => ∫ y, Dt (n + 1) (Preorder.frestrictLe (n + 1) y)
        ∂(Kernel.traj (stepKernel G σ) n (Preorder.frestrictLe n r)) :=
    (condExp_congr_ae (hYeq (n + 1))).trans
      (Kernel.condExp_traj (κ := stepKernel G σ) (Nat.zero_le n) (hintt (n + 1)))
  filter_upwards [hce, hfeas] with r hr hfr
  rw [hr, integral_step G σ n _ (Dt (n + 1)) C (hDt_bd (n + 1))]
  set h := Preorder.frestrictLe n r
  have hhf : Feasible G h := hfr n
  have key := (h2 n h hhf).trans (minmax_le_of_eq G D h (x n h) (hx n h hhf) i)
  refine key.trans (le_of_eq ?_)
  unfold oneShotPayoff oneShotPayoffPure
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
  congr 1
  refine tsum_congr fun s' => ?_
  by_cases hp : G.p (lastState h) a s' = 0
  · simp [hp]
  · rw [hDt_eq _ _ (feasible_extend G h hhf a s' (pos_iff_ne_zero.2 hp))]
