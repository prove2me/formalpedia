-- Prove2me | solution 1 for DimdPolyLEAN.lowAnnulusDefectControl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:58.426541+00:00
-- url     : https://prove2.me/submissions/8610188b-0781-4e82-ba18-dd7d010ad4a4

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Theorems.Thm_DimdPolyLEAN_annulusMassPartition
public import Theorems.Thm_DimdPolyLEAN_exact_modulus_recovery_skappa_ae
public import Theorems.Thm_DimdPolyLEAN_lowAnnulusProjection
public import Theorems.Thm_DimdPolyLEAN_summable_skappa_eval_mul
public import Theorems.Thm_DimdPolyLEAN_summable_sq_Phi_eval
public import Theorems.Thm_DimdPolyLEAN_toFun_ofPkappa
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem norm_sq_eq_sum_coeff_wip
    {d : Nat} {kappa : MultiIndex d} (H : Pkappa d kappa) :
    ‖H‖ ^ 2 = Finset.sum H.support (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
  unfold coeffPkappa
  change (Real.sqrt (Finset.sum H.support (fun alpha => ‖H alpha‖ ^ 2))) ^ 2 = _
  rw [Real.sq_sqrt]
  positivity
private theorem toFun_ofPkappa_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  exact toFun_ofPkappa kappa F
private theorem finite_eval_sum_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (E : Finset (Idx d)) (z : Cd d) :
    Filter.Tendsto
      (fun m => Finset.sum E
        (fun alpha => coeffPkappa (H m) alpha * Phi kappa alpha z))
      Filter.atTop
      (nhds (Finset.sum E
        (fun alpha => coeffSkappa U alpha * Phi kappa alpha z))) := by
  apply tendsto_finsetSum
  intro alpha halpha
  exact (hcoeff alpha).mul tendsto_const_nhds
private theorem summable_sq_Phi_eval_wip
    {d : Nat} (kappa : MultiIndex d) (z : Cd d) :
    Summable (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) := by
  exact summable_sq_Phi_eval kappa z
private theorem summable_skappa_eval_mul_wip
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha z) := by
  exact summable_skappa_eval_mul kappa U z
private theorem summable_pkappa_eval_mul_wip
    {d : Nat} (kappa : MultiIndex d) (H : Pkappa d kappa) (z : Cd d) :
    Summable (fun alpha : Idx d => coeffPkappa H alpha * Phi kappa alpha z) := by
  have h := summable_skappa_eval_mul_wip kappa (ofPkappa kappa H) z
  refine h.congr ?_
  intro alpha
  rfl
private theorem evalPkappa_eq_tsum_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (H : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa H z =
      ∑' alpha : Idx d, coeffPkappa H alpha * Phi kappa alpha z := by
  have h := congrFun (toFun_ofPkappa_wip kappa H) z
  exact h.symm
private theorem evalPkappa_sub_toFun_eq_tsum_diff_wip
    {d : Nat} (kappa : MultiIndex d) (H : Pkappa d kappa)
    (U : Skappa d kappa) (z : Cd d) :
    evalPkappa kappa H z - toFun kappa U z =
      ∑' alpha : Idx d,
        (coeffPkappa H alpha - coeffSkappa U alpha) * Phi kappa alpha z := by
  have hHsum := summable_pkappa_eval_mul_wip kappa H z
  have hUsum := summable_skappa_eval_mul_wip kappa U z
  rw [evalPkappa_eq_tsum_coeff_wip, toFun]
  have hsub := hHsum.tsum_sub hUsum
  have hdiff_eq :
      (∑' alpha : Idx d,
        (coeffPkappa H alpha - coeffSkappa U alpha) * Phi kappa alpha z) =
        ∑' alpha : Idx d,
          (coeffPkappa H alpha * Phi kappa alpha z -
            coeffSkappa U alpha * Phi kappa alpha z) := tsum_congr fun alpha => by ring
  rw [hdiff_eq, hsub]
private theorem evalPkappa_add_apply_wip
    {d : Nat} (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa (F + G) z = evalPkappa kappa F z + evalPkappa kappa G z := by
  unfold evalPkappa
  rw [Finsupp.sum_add_index'] <;> simp [add_mul]
private theorem evalPkappa_smul_real_wip
    {d : Nat} (kappa : MultiIndex d) (t : ℝ) (H : Pkappa d kappa) :
    evalPkappa kappa (t • H) = fun z => (t : ℂ) * evalPkappa kappa H z := by
  ext z
  by_cases ht : t = 0
  · subst t
    simp [evalPkappa]
  · unfold evalPkappa
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq ht, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    rw [Finsupp.smul_apply]
    change ((t : ℂ) * H alpha) * Phi kappa alpha z =
      (t : ℂ) * (H alpha * Phi kappa alpha z)
    ring
private theorem finite_eval_sum_norm_le_wip
    {d : Nat} (kappa : MultiIndex d) (E : Finset (Idx d))
    (a : Idx d -> ℂ) (z : Cd d) :
    ‖Finset.sum E (fun alpha => a alpha * Phi kappa alpha z)‖ <=
      Real.sqrt (Finset.sum E (fun alpha => ‖a alpha‖ ^ 2)) *
        Real.sqrt (Finset.sum E (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := by
  calc
    ‖Finset.sum E (fun alpha => a alpha * Phi kappa alpha z)‖
        <= Finset.sum E (fun alpha => ‖a alpha * Phi kappa alpha z‖) :=
          norm_sum_le E (fun alpha => a alpha * Phi kappa alpha z)
    _ = Finset.sum E (fun alpha => ‖a alpha‖ * ‖Phi kappa alpha z‖) := by
          simp_all
    _ <= Real.sqrt (Finset.sum E (fun alpha => ‖a alpha‖ ^ 2)) *
        Real.sqrt (Finset.sum E (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := by
          simpa using
            Real.sum_mul_le_sqrt_mul_sqrt E
              (fun alpha => ‖a alpha‖) (fun alpha => ‖Phi kappa alpha z‖)
private theorem evalPkappa_norm_le_kernel_sqrt_wip
    {d : Nat} (kappa : MultiIndex d) (H : Pkappa d kappa)
    (hH_norm : ‖H‖ = 1) (z : Cd d) :
    ‖evalPkappa kappa H z‖ <=
      Real.sqrt (∑' alpha : Idx d, ‖Phi kappa alpha z‖ ^ 2) := by
  have hfinite :=
    finite_eval_sum_norm_le_wip kappa H.support (coeffPkappa H) z
  have hcoeff_sqrt :
      Real.sqrt (Finset.sum H.support
        (fun alpha => ‖coeffPkappa H alpha‖ ^ 2)) = 1 := by
    have hnorm_sq := norm_sq_eq_sum_coeff_wip H
    have hsum_eq_one :
        Finset.sum H.support (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) = 1 := by
      nlinarith only [hH_norm, hnorm_sq]
    simp_all
  have hphi_le :
      Finset.sum H.support (fun alpha => ‖Phi kappa alpha z‖ ^ 2) <=
        ∑' alpha : Idx d, ‖Phi kappa alpha z‖ ^ 2 := by
    exact (summable_sq_Phi_eval_wip kappa z).sum_le_tsum _
      (fun alpha halpha => sq_nonneg _)
  have hsqrt_le := Real.sqrt_le_sqrt hphi_le
  calc
    ‖evalPkappa kappa H z‖
        = ‖Finset.sum H.support
            (fun alpha => coeffPkappa H alpha * Phi kappa alpha z)‖ := by rfl
    _ <= Real.sqrt (Finset.sum H.support
          (fun alpha => ‖coeffPkappa H alpha‖ ^ 2)) *
        Real.sqrt (Finset.sum H.support
          (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := hfinite
    _ = Real.sqrt (Finset.sum H.support
          (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := by rw [hcoeff_sqrt, one_mul]
    _ <= Real.sqrt (∑' alpha : Idx d, ‖Phi kappa alpha z‖ ^ 2) := hsqrt_le
private theorem finite_coeff_sum_le_norm_sq_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (H : Pkappa d kappa) :
    Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <= ‖H‖ ^ 2 := by
  classical
  rw [norm_sq_eq_sum_coeff_wip H]
  have hsum_eq :
      Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) =
        Finset.sum (E ∩ H.support) (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    symm
    refine Finset.sum_subset (by intro alpha h; exact (Finset.mem_inter.mp h).1) ?_
    intro alpha hE hnot
    have hnot_support : alpha ∉ H.support := by
      simp_all
    simp [coeffPkappa, Finsupp.notMem_support_iff.mp hnot_support]
  rw [hsum_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro alpha h; exact (Finset.mem_inter.mp h).2)
    (by intro alpha hsupport hnot; positivity)
private theorem finite_coeff_diff_sq_sum_le_four_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d))
    {H : Pkappa d kappa} {U : Skappa d kappa}
    (hH_norm : ‖H‖ = 1)
    (hU_partial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) :
    Finset.sum E (fun alpha => ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2) <= 4 := by
  have hterm :
      ∀ alpha : Idx d,
        ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2 <=
          (2 : ℝ) * (‖coeffPkappa H alpha‖ ^ 2 + ‖coeffSkappa U alpha‖ ^ 2) := by
    intro alpha
    have hsub :
        ‖coeffPkappa H alpha - coeffSkappa U alpha‖ <=
          ‖coeffPkappa H alpha‖ + ‖coeffSkappa U alpha‖ := norm_sub_le _ _
    have hsq :
        ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2 <=
          (‖coeffPkappa H alpha‖ + ‖coeffSkappa U alpha‖) ^ 2 := by
      nlinarith only [
        hsub, norm_nonneg (coeffPkappa H alpha - coeffSkappa U alpha),
        norm_nonneg (coeffPkappa H alpha), norm_nonneg (coeffSkappa U alpha)
      ]
    have ham :
        (‖coeffPkappa H alpha‖ + ‖coeffSkappa U alpha‖) ^ 2 <=
          2 * (‖coeffPkappa H alpha‖ ^ 2 + ‖coeffSkappa U alpha‖ ^ 2) := by
      linarith only [sq_nonneg (‖coeffPkappa H alpha‖ - ‖coeffSkappa U alpha‖)]
    exact le_trans hsq ham
  calc
    Finset.sum E (fun alpha => ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2)
        <= Finset.sum E
          (fun alpha => (2 : ℝ) *
            (‖coeffPkappa H alpha‖ ^ 2 + ‖coeffSkappa U alpha‖ ^ 2)) :=
          Finset.sum_le_sum fun alpha halpha => hterm alpha
    _ = Finset.sum E
          (fun alpha => 2 * ‖coeffPkappa H alpha‖ ^ 2 +
            2 * ‖coeffSkappa U alpha‖ ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro alpha halpha
          ring
    _ = 2 * Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) +
          2 * Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ <= 2 * 1 + 2 * 1 := by
          have hH_le : Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <= 1 := by
            have hle := finite_coeff_sum_le_norm_sq_wip E H
            simp_all
          have hU_le := hU_partial E
          linarith only [hH_le, hU_le]
    _ = 4 := by ring
private theorem finite_eval_diff_sum_norm_le_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d))
    {H : Pkappa d kappa} {U : Skappa d kappa}
    (hH_norm : ‖H‖ = 1)
    (hU_partial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (z : Cd d) :
    ‖Finset.sum E
      (fun alpha => (coeffPkappa H alpha - coeffSkappa U alpha) * Phi kappa alpha z)‖ <=
      2 * Real.sqrt (Finset.sum E (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := by
  have hcs := finite_eval_sum_norm_le_wip kappa E
    (fun alpha => coeffPkappa H alpha - coeffSkappa U alpha) z
  have hdiff := finite_coeff_diff_sq_sum_le_four_wip E hH_norm hU_partial
  have hsqrt_le_two :
      Real.sqrt (Finset.sum E
        (fun alpha => ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2)) <= 2 := by
    calc
      Real.sqrt (Finset.sum E
        (fun alpha => ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2))
          <= Real.sqrt 4 := Real.sqrt_le_sqrt hdiff
      _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
  have hphi_nonneg :
      0 <= Real.sqrt (Finset.sum E (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) :=
    Real.sqrt_nonneg _
  exact le_trans hcs (by nlinarith only [hsqrt_le_two, hphi_nonneg])
private theorem phi_sq_finite_tail_small_wip
    {d : Nat} (kappa : MultiIndex d) (z : Cd d) {eps : ℝ} (heps : 0 < eps) :
    ∃ E : Finset (Idx d), ∀ T : Finset (Idx d),
      Disjoint T E ->
        Finset.sum T (fun alpha => ‖Phi kappa alpha z‖ ^ 2) < eps := by
  obtain ⟨E, hE⟩ :=
    (summable_iff_vanishing_norm.mp (summable_sq_Phi_eval_wip kappa z)) eps heps
  refine ⟨E, ?_⟩
  intro T hdis
  have h := hE T hdis
  have hnonneg : 0 <= Finset.sum T (fun alpha => ‖Phi kappa alpha z‖ ^ 2) :=
    Finset.sum_nonneg fun alpha halpha => sq_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using h
private theorem finite_eval_diff_tail_small_wip
    {d : Nat} (kappa : MultiIndex d) (z : Cd d) {eps : ℝ} (heps : 0 < eps) :
    ∃ E : Finset (Idx d), ∀ T : Finset (Idx d),
      Disjoint T E ->
      ∀ {H : Pkappa d kappa} {U : Skappa d kappa},
        ‖H‖ = 1 ->
        (∀ E : Finset (Idx d),
          Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ->
        ‖Finset.sum T
          (fun alpha => (coeffPkappa H alpha - coeffSkappa U alpha) *
            Phi kappa alpha z)‖ < eps := by
  obtain ⟨E, hE⟩ :=
    phi_sq_finite_tail_small_wip kappa z
      (by positivity : 0 < (eps / 2) ^ 2)
  refine ⟨E, ?_⟩
  intro T hdis H U hH_norm hU_partial
  have htail := hE T hdis
  have htail_nonneg :
      0 <= Finset.sum T (fun alpha => ‖Phi kappa alpha z‖ ^ 2) :=
    Finset.sum_nonneg fun alpha halpha => sq_nonneg _
  have hsqrt_lt :
      Real.sqrt (Finset.sum T (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) < eps / 2 := by
    rw [← Real.sqrt_sq (by linarith only [heps] : 0 <= eps / 2)]
    exact Real.sqrt_lt_sqrt htail_nonneg htail
  have hbound := finite_eval_diff_sum_norm_le_wip T hH_norm hU_partial z
  linarith only [hsqrt_lt, hbound]
private theorem norm_tsum_subtype_compl_le_of_finset_bound_wip
    {ι : Type*} (E : Finset ι) {f : ι -> ℂ} {C : ℝ}
    (hf : Summable (fun alpha : {alpha // alpha ∉ (E : Set ι)} => f alpha))
    (hC : ∀ T : Finset ι, Disjoint T E -> ‖Finset.sum T f‖ <= C) :
    ‖∑' alpha : {alpha // alpha ∉ (E : Set ι)}, f alpha‖ <= C := by
  classical
  have hlim := hf.hasSum.norm
  refine le_of_tendsto hlim (Filter.Eventually.of_forall ?_)
  intro T
  let T' : Finset ι := T.map ⟨Subtype.val, Subtype.coe_injective⟩
  have hdis : Disjoint T' E := by
    rw [Finset.disjoint_left]
    intro alpha halpha hE
    rcases Finset.mem_map.mp halpha with ⟨beta, hbeta, rfl⟩
    exact beta.2 hE
  have hsum :
      Finset.sum T (fun alpha : {alpha // alpha ∉ (E : Set ι)} => f alpha) =
        Finset.sum T' f := by simp [T']
  simp_all only []
private theorem evalPkappa_tendsto_toFun_of_coeff_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hU_partial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (z : Cd d) :
    Filter.Tendsto (fun m => evalPkappa kappa (H m) z) Filter.atTop
      (nhds (toFun kappa U z)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨E, hE⟩ :=
    finite_eval_diff_tail_small_wip kappa z (by linarith only [heps] : 0 < eps / 3)
  have hhead :
      Filter.Tendsto
        (fun m => Finset.sum E
          (fun alpha =>
            (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z))
        Filter.atTop (nhds 0) := by
    have hsum := finite_eval_sum_tendsto_wip hcoeff E z
    have hsub :
        Filter.Tendsto
          (fun m =>
            Finset.sum E (fun alpha => coeffPkappa (H m) alpha * Phi kappa alpha z) -
              Finset.sum E (fun alpha => coeffSkappa U alpha * Phi kappa alpha z))
          Filter.atTop
          (nhds
            (Finset.sum E (fun alpha => coeffSkappa U alpha * Phi kappa alpha z) -
              Finset.sum E (fun alpha => coeffSkappa U alpha * Phi kappa alpha z))) :=
      hsum.sub tendsto_const_nhds
    convert hsub using 1
    · ext m
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro alpha halpha
      ring
    · simp
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hhead) (eps / 3) (by linarith only [heps])
  refine ⟨M, ?_⟩
  intro m hm
  rw [dist_eq_norm]
  have hdiff_summ :
      Summable (fun alpha : Idx d =>
        (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z) := by
    have hHsum := summable_pkappa_eval_mul_wip kappa (H m) z
    have hUsum := summable_skappa_eval_mul_wip kappa U z
    exact (hHsum.sub hUsum).congr fun alpha => by ring
  have htail_le :
      ‖∑' alpha : {alpha // alpha ∉ (E : Set (Idx d))},
        (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z‖ <=
        eps / 3 := by
    refine norm_tsum_subtype_compl_le_of_finset_bound_wip
      (E := E)
      (f := fun alpha : Idx d =>
        (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z)
      (hf := hdiff_summ.subtype _) ?_
    intro T hdis
    exact le_of_lt (hE T hdis (hH_norm m) hU_partial)
  have hsplit := hdiff_summ.sum_add_tsum_subtype_compl E
  have hdiff_eval := evalPkappa_sub_toFun_eq_tsum_diff_wip kappa (H m) U z
  rw [hdiff_eval, ← hsplit]
  have hhead_lt :
      ‖Finset.sum E
        (fun alpha =>
          (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z)‖ <
        eps / 3 := by simpa [dist_eq_norm] using hM m hm
  have hsum_norm :=
    norm_add_le
      (Finset.sum E
        (fun alpha =>
          (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z))
      (∑' alpha : {alpha // alpha ∉ (E : Set (Idx d))},
        (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z)
  calc
    ‖Finset.sum E
        (fun alpha =>
          (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z) +
        ∑' alpha : {alpha // alpha ∉ (E : Set (Idx d))},
          (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z‖
        <=
        ‖Finset.sum E
          (fun alpha =>
            (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z)‖ +
          ‖∑' alpha : {alpha // alpha ∉ (E : Set (Idx d))},
            (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z‖ :=
          hsum_norm
    _ < eps / 3 + eps / 3 := add_lt_add_of_lt_of_le hhead_lt htail_le
    _ < eps := by linarith only [heps]
private theorem evalPkappa_add_smul_tendsto_toFun_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa)
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    {t : ℕ -> ℝ} {T : ℝ}
    (ht : Filter.Tendsto t Filter.atTop (nhds T))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hU_partial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (z : Cd d) :
    Filter.Tendsto
      (fun m => evalPkappa kappa (F + t m • H m) z)
      Filter.atTop
      (nhds (evalPkappa kappa F z + (T : ℂ) * toFun kappa U z)) := by
  have hH_eval :=
    evalPkappa_tendsto_toFun_of_coeff_tendsto_wip hcoeff hH_norm hU_partial z
  have ht_complex :
      Filter.Tendsto (fun m => (t m : ℂ)) Filter.atTop (nhds (T : ℂ)) :=
    (Complex.continuous_ofReal.tendsto T).comp ht
  have hscaled :=
    ht_complex.mul hH_eval
  have hconst :
      Filter.Tendsto (fun _ : ℕ => evalPkappa kappa F z) Filter.atTop
        (nhds (evalPkappa kappa F z)) :=
    tendsto_const_nhds
  have hsum := hconst.add hscaled
  convert hsum using 1
  ext m
  rw [evalPkappa_add_apply_wip, congrFun (evalPkappa_smul_real_wip kappa (t m) (H m)) z]
private theorem ae_norm_eq_of_tendsto_defect_wip
    {d : Nat} {base : Cd d -> ℂ}
    {v : ℕ -> Cd d -> ℂ} {limit : Cd d -> ℂ}
    (hpointwise :
      ∀ᵐ z ∂ gammaD d, Filter.Tendsto (fun m => v m z) Filter.atTop (nhds (limit z)))
    (hdefect :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m => |‖v m z‖ - ‖base z‖|)
          Filter.atTop (nhds 0)) :
    (fun z => ‖limit z‖) =ᵐ[gammaD d] fun z => ‖base z‖ := by
  filter_upwards [hpointwise, hdefect] with z hzpoint hzdef
  let φ : ℂ -> ℝ := fun w => |‖w‖ - ‖base z‖|
  have hφ : Continuous φ := by
    unfold φ
    exact (continuous_norm.sub continuous_const).abs
  have hlim :
      Filter.Tendsto
        (fun m => |‖v m z‖ - ‖base z‖|)
        Filter.atTop
        (nhds (|‖limit z‖ - ‖base z‖|)) := by
    change Filter.Tendsto (φ ∘ fun m => v m z) Filter.atTop (nhds (φ (limit z)))
    exact (hφ.tendsto (limit z)).comp hzpoint
  have hzero : |‖limit z‖ - ‖base z‖| = 0 :=
    tendsto_nhds_unique hlim hzdef
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
private theorem ae_real_part_eq_zero_of_tendsto_wip
    {d : Nat} {base : Cd d -> ℂ}
    {u : ℕ -> Cd d -> ℂ} {limit : Cd d -> ℂ}
    (hpointwise :
      ∀ᵐ z ∂ gammaD d, Filter.Tendsto (fun m => u m z) Filter.atTop (nhds (limit z)))
    (hreal :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m => Complex.re (u m z * star (base z)))
          Filter.atTop (nhds 0)) :
    (fun z => Complex.re (limit z * star (base z))) =ᵐ[gammaD d] fun _ => 0 := by
  filter_upwards [hpointwise, hreal] with z hzpoint hzreal
  let φ : ℂ -> ℝ := fun w => Complex.re (w * star (base z))
  have hφ : Continuous φ := by
    unfold φ
    exact Complex.continuous_re.comp (continuous_id.mul continuous_const)
  have hlim :
      Filter.Tendsto
        (fun m => Complex.re (u m z * star (base z)))
        Filter.atTop
        (nhds (Complex.re (limit z * star (base z)))) := by
    change Filter.Tendsto (φ ∘ fun m => u m z) Filter.atTop (nhds (φ (limit z)))
    exact (hφ.tendsto (limit z)).comp hzpoint
  exact tendsto_nhds_unique hlim hzreal
private theorem pkappaInner_eq_sum_right_support_wip
    {d : Nat} {kappa : MultiIndex d} (G F : Pkappa d kappa) :
    pkappaInner G F = Finset.sum F.support (fun alpha => G alpha * star (F alpha)) := by
  classical
  unfold pkappaInner
  rw [Finsupp.sum]
  have hleft :
      Finset.sum G.support (fun alpha => G alpha * star (F alpha)) =
        Finset.sum (G.support ∩ F.support) (fun alpha => G alpha * star (F alpha)) := by
    symm
    refine Finset.sum_subset (by intro alpha h; exact (Finset.mem_inter.mp h).1) ?_
    simp_all
  have hright :
      Finset.sum F.support (fun alpha => G alpha * star (F alpha)) =
        Finset.sum (G.support ∩ F.support) (fun alpha => G alpha * star (F alpha)) := by
    symm
    refine Finset.sum_subset (by intro alpha h; exact (Finset.mem_inter.mp h).2) ?_
    simp_all
  exact hleft.trans hright.symm
private theorem orthogonalToSkappa_of_coeff_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (horth : ∀ m, orthogonalToPk F (H m))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha))) :
    orthogonalToSkappa_wip F U := by
  have hsum_tendsto :
      Filter.Tendsto
        (fun m =>
          Finset.sum F.support
            (fun alpha => coeffPkappa (H m) alpha * star (coeffPkappa F alpha)))
        Filter.atTop
        (nhds (Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)))) := by
    apply tendsto_finsetSum
    intro alpha halpha
    exact (hcoeff alpha).mul tendsto_const_nhds
  have hsum_zero :
      (fun m =>
          Finset.sum F.support
            (fun alpha => coeffPkappa (H m) alpha * star (coeffPkappa F alpha))) =
        fun _ : ℕ => (0 : ℂ) := by
    funext m
    have hm := horth m
    dsimp [orthogonalToPk] at hm
    simpa [coeffPkappa, pkappaInner_eq_sum_right_support_wip (H m) F] using hm
  have hzero_tendsto :
      Filter.Tendsto
        (fun m =>
          Finset.sum F.support
            (fun alpha => coeffPkappa (H m) alpha * star (coeffPkappa F alpha)))
        Filter.atTop (nhds (0 : ℂ)) := by
    simp_all
  exact tendsto_nhds_unique hsum_tendsto hzero_tendsto
private theorem scalar_multiple_eq_zero_of_orthogonalToSkappa_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {U : Skappa d kappa} {c : ℂ}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha)
    (horth : orthogonalToSkappa_wip F U) :
    c = 0 := by
  have hinner :
      Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)) =
        c * ((Finset.sum F.support
          (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) := by
    calc
      Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha))
          = Finset.sum F.support
            (fun alpha => (c * coeffPkappa F alpha) * star (coeffPkappa F alpha)) := by
              simp_all
      _ = c * Finset.sum F.support
            (fun alpha => coeffPkappa F alpha * star (coeffPkappa F alpha)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              ring
      _ = c * ((Finset.sum F.support
            (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) := by
              congr 1
              norm_num
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              simpa [Complex.normSq_eq_norm_sq] using
                Complex.mul_conj (coeffPkappa F alpha)
  have hsum_one :
      ((Finset.sum F.support (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) = 1 := by
    have hnorm_sq := norm_sq_eq_sum_coeff_wip F
    have hF_sq : ‖F‖ ^ 2 = 1 := by nlinarith only [hF_norm]
    norm_num
    exact_mod_cast hnorm_sq.symm.trans hF_sq
  have hzero : c * ((Finset.sum F.support
      (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) = 0 := by rw [← hinner, horth]
  simpa [hsum_one] using hzero
private theorem coeff_zero_of_scalar_multiple_orthogonalToSkappa_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {U : Skappa d kappa} {c : ℂ}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha)
    (horth : orthogonalToSkappa_wip F U) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  have hc : c = 0 :=
    scalar_multiple_eq_zero_of_orthogonalToSkappa_wip hF_norm hcoeff horth
  simp_all
private theorem finite_coeff_sq_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (E : Finset (Idx d)) :
    Filter.Tendsto
      (fun m => Finset.sum E (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2))
      Filter.atTop
      (nhds (Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2))) := by
  apply tendsto_finsetSum
  intro alpha halpha
  exact ((continuous_pow 2).tendsto _).comp ((hcoeff alpha).norm)
private theorem finite_coeff_sq_limit_ge_of_forall_le_wip
    {d : Nat} {kappa : MultiIndex d}
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    {rho : ℝ} (E : Finset (Idx d))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (hmass : ∀ m, rho <=
      Finset.sum E (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2)) :
    rho <= Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
  exact ge_of_tendsto (finite_coeff_sq_tendsto_wip hcoeff E)
    (Filter.Eventually.of_forall hmass)
private theorem coeff_limit_subseq_with_head_mass_wip
    {d : Nat} (kappa : MultiIndex d)
    (K : Finset (Idx d)) {rho : ℝ}
    (H : ℕ -> Pkappa d kappa)
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hmass : ∀ m, rho <=
      Finset.sum K (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2)) :
    ∃ U : Skappa d kappa, ∃ φ : ℕ -> ℕ,
      StrictMono φ ∧
      (∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha) Filter.atTop
        (nhds (coeffSkappa U alpha))) ∧
      (∀ E : Finset (Idx d),
        Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ∧
      rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
  let S : Set (Idx d -> ℂ) :=
    {x | ∀ alpha, x alpha ∈ Metric.closedBall (0 : ℂ) 1}
  have hcoeff_le_one : ∀ m alpha, ‖coeffPkappa (H m) alpha‖ <= 1 := by
    intro m alpha
    have hle :=
      finite_coeff_sum_le_norm_sq_wip ({alpha} : Finset (Idx d)) (H m)
    simp_all
  have hseq_mem : ∀ m, (fun alpha => coeffPkappa (H m) alpha) ∈ S := by
    intro m alpha
    simpa only [S, Metric.mem_closedBall, dist_zero_right] using hcoeff_le_one m alpha
  have hS_compact : IsCompact S := by
    dsimp [S]
    exact isCompact_pi_infinite
      (fun _ : Idx d => ProperSpace.isCompact_closedBall (0 : ℂ) 1)
  have hS_seqcompact : IsSeqCompact S := hS_compact.isSeqCompact
  obtain ⟨u, _hu_mem, φ, hφ_strict, hφ_tendsto⟩ :=
    hS_seqcompact (fun m => hseq_mem m)
  have hcoeff_raw :
      ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
        Filter.atTop (nhds (u alpha)) := by
    intro alpha
    exact (continuous_apply alpha |>.tendsto u).comp hφ_tendsto
  have hfinite_tendsto :
      ∀ E : Finset (Idx d),
        Filter.Tendsto
          (fun m => Finset.sum E (fun alpha => ‖coeffPkappa (H (φ m)) alpha‖ ^ 2))
          Filter.atTop
          (nhds (Finset.sum E (fun alpha => ‖u alpha‖ ^ 2))) := by
    intro E
    apply tendsto_finsetSum
    intro alpha halpha
    exact ((continuous_pow 2).tendsto _).comp ((hcoeff_raw alpha).norm)
  have hpartial :
      ∀ E : Finset (Idx d), Finset.sum E (fun alpha => ‖u alpha‖ ^ 2) <= 1 := by
    intro E
    refine le_of_tendsto (hfinite_tendsto E) (Filter.Eventually.of_forall ?_)
    intro m
    have hle := finite_coeff_sum_le_norm_sq_wip E (H (φ m))
    simp_all
  let U : Skappa d kappa := skappaOfCoeffBound_wip kappa u hpartial
  have hcoeff :
      ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
        Filter.atTop (nhds (coeffSkappa U alpha)) := by
    intro alpha
    simpa [U, skappaOfCoeffBound_wip, coeffSkappa] using hcoeff_raw alpha
  have hpartial_U :
      ∀ E : Finset (Idx d),
        Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1 := by
    intro E
    simpa [U, skappaOfCoeffBound_wip, coeffSkappa] using hpartial E
  have hmass_U : rho <=
      Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
    exact finite_coeff_sq_limit_ge_of_forall_le_wip K hcoeff
      (fun m => hmass (φ m))
  exact ⟨U, φ, hφ_strict, hcoeff, hpartial_U, hmass_U⟩
private theorem scalar_coeff_limit_subseq_with_head_mass_wip
    {d : Nat} (kappa : MultiIndex d)
    (K : Finset (Idx d)) {rho : ℝ}
    (H : ℕ -> Pkappa d kappa) (t : ℕ -> ℝ)
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hmass : ∀ m, rho <=
      Finset.sum K (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2))
    (ht_mem : ∀ m, t m ∈ Set.Icc (0 : ℝ) 4) :
    ∃ T : ℝ, ∃ U : Skappa d kappa, ∃ φ : ℕ -> ℕ,
      T ∈ Set.Icc (0 : ℝ) 4 ∧
      StrictMono φ ∧
      Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T) ∧
      (∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha) Filter.atTop
        (nhds (coeffSkappa U alpha))) ∧
      (∀ E : Finset (Idx d),
        Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ∧
      rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
  obtain ⟨T, hT_closure, ψ, hψ_strict, hψ_tendsto⟩ :=
    tendsto_subseq_of_bounded
      (s := Set.Icc (0 : ℝ) 4)
      (Metric.isBounded_Icc (0 : ℝ) 4)
      ht_mem
  have hT_mem : T ∈ Set.Icc (0 : ℝ) 4 := by simpa [closure_Icc] using hT_closure
  obtain ⟨U, φ, hφ_strict, hcoeff, hpartial, hmass_U⟩ :=
    coeff_limit_subseq_with_head_mass_wip kappa K
      (fun m => H (ψ m))
      (fun m => hH_norm (ψ m))
      (fun m => hmass (ψ m))
  let σ : ℕ -> ℕ := fun m => ψ (φ m)
  have hσ_strict : StrictMono σ := by exact hψ_strict.comp hφ_strict
  have hσ_t_tendsto :
      Filter.Tendsto (fun m => t (σ m)) Filter.atTop (nhds T) :=
    hψ_tendsto.comp hφ_strict.tendsto_atTop
  have hσ_coeff :
      ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (σ m)) alpha)
        Filter.atTop (nhds (coeffSkappa U alpha)) := by
    intro alpha
    exact hcoeff alpha
  exact ⟨T, U, σ, hT_mem, hσ_strict, hσ_t_tendsto, hσ_coeff, hpartial, hmass_U⟩
private theorem finite_head_mass_contradiction_of_coeff_zero_wip
    {d : Nat} {kappa : MultiIndex d} (K : Finset (Idx d)) {rho : ℝ}
    (h_rho : 0 < rho) {U : Skappa d kappa}
    (hmass : rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2))
    (hzero : ∀ alpha, coeffSkappa U alpha = 0) :
    False := by
  have hsum_zero :
      Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) = 0 := by simp [hzero]
  linarith only [h_rho, hmass, hsum_zero]
private theorem bad_sequence_of_no_finite_head_lower_bound_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (K : Finset (Idx d)) (rho : ℝ)
    (hbad :
      ¬ ∃ delta : ℝ, 0 < delta ∧
        ∀ {H : Pkappa d kappa} {t : ℝ},
          orthogonalToPk F H ->
          ‖H‖ = 1 ->
          rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
          0 < t ->
          t <= 4 ->
          delta * t <= defect F (t • H)) :
    ∀ n : ℕ, ∃ H : Pkappa d kappa, ∃ t : ℝ,
      orthogonalToPk F H ∧
      ‖H‖ = 1 ∧
      rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ∧
      0 < t ∧
      t <= 4 ∧
      defect F (t • H) < (1 / ((n + 1 : Nat) : ℝ)) * t := by
  intro n
  let delta : ℝ := 1 / ((n + 1 : Nat) : ℝ)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  by_contra hno
  apply hbad
  refine ⟨delta, hdelta_pos, ?_⟩
  intro H t horth hH_norm hmass ht_pos ht_le_four
  by_contra hnot
  have hlt : defect F (t • H) < delta * t := lt_of_not_ge hnot
  exact hno ⟨H, t, horth, hH_norm, hmass, ht_pos, ht_le_four, hlt⟩
private theorem finite_head_bad_limit_data_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (K : Finset (Idx d)) {rho : ℝ}
    (hbad :
      ¬ ∃ delta : ℝ, 0 < delta ∧
        ∀ {H : Pkappa d kappa} {t : ℝ},
          orthogonalToPk F H ->
          ‖H‖ = 1 ->
          rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
          0 < t ->
          t <= 4 ->
          delta * t <= defect F (t • H)) :
    ∃ H : ℕ -> Pkappa d kappa, ∃ t : ℕ -> ℝ,
      ∃ T : ℝ, ∃ U : Skappa d kappa, ∃ φ : ℕ -> ℕ,
        T ∈ Set.Icc (0 : ℝ) 4 ∧
        StrictMono φ ∧
        Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T) ∧
        (∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
          Filter.atTop (nhds (coeffSkappa U alpha))) ∧
        (∀ E : Finset (Idx d),
          Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ∧
        rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) ∧
        (∀ m, orthogonalToPk F (H m)) ∧
        (∀ m, ‖H m‖ = 1) ∧
        (∀ m, rho <= Finset.sum K (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2)) ∧
        (∀ m, 0 < t m) ∧
        (∀ m, t m <= 4) ∧
        (∀ m, defect F (t m • H m) <
          (1 / ((m + 1 : Nat) : ℝ)) * t m) ∧
        orthogonalToSkappa_wip F U := by
  have hseq := bad_sequence_of_no_finite_head_lower_bound_wip F K rho hbad
  choose H t horth hH_norm hmass ht_pos ht_le hdef using hseq
  have ht_mem : ∀ m, t m ∈ Set.Icc (0 : ℝ) 4 := by
    intro m
    exact Set.mem_Icc.mpr ⟨le_of_lt (ht_pos m), ht_le m⟩
  obtain ⟨T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial, hmass_U⟩ :=
    scalar_coeff_limit_subseq_with_head_mass_wip kappa K H t hH_norm hmass ht_mem
  have horth_U : orthogonalToSkappa_wip F U := by
    exact orthogonalToSkappa_of_coeff_tendsto_wip
      (F := F) (H := fun m => H (φ m)) (U := U)
      (fun m => horth (φ m)) hcoeff
  exact
    ⟨H, t, T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial,
      hmass_U, horth, hH_norm, hmass, ht_pos, ht_le, hdef, horth_U⟩
private theorem defect_nonneg_wip
    {d : Nat} {kappa : MultiIndex d}
    (F G : Pkappa d kappa) :
    0 <= defect F G := Real.sqrt_nonneg _
private lemma continuous_evalPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  exact continuous_evalPkappa kappa F
private lemma norm_sq_add_real_smul_wip (a w : ℂ) (t : ℝ) :
    ‖a + (t : ℂ) * w‖ ^ 2 =
      ‖a‖ ^ 2 + t ^ 2 * ‖w‖ ^ 2 + 2 * t * Complex.re (w * star a) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, ← Complex.normSq_eq_norm_sq]
  have hsq : Complex.normSq ((t : ℂ) * w) = t ^ 2 * ‖w‖ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    ring
  rw [hsq]
  have hre :
      Complex.re (a * star ((t : ℂ) * w)) = t * Complex.re (w * star a) := by
    have hstar : star ((t : ℂ) * w) = (t : ℂ) * star w := by simp
    rw [hstar]
    have hmul : a * ((t : ℂ) * star w) = (a * star w) * (t : ℂ) := by ring
    rw [hmul, Complex.re_mul_ofReal]
    have hre' : Complex.re (a * star w) = Complex.re (w * star a) := by
      simp [Complex.mul_re, sub_eq_add_neg, mul_comm]
    rw [hre']
    ring
  have hre' :
      (a * (starRingEnd ℂ) ((t : ℂ) * w)).re =
        t * Complex.re (w * star a) := by exact hre
  rw [hre']
  ring
private lemma defectFunction_div_eq_abs_linearization_wip
    (a w : ℂ) {t : ℝ} (ht : 0 < t) :
    |‖a + (t : ℂ) * w‖ - ‖a‖| / t *
        (‖a + (t : ℂ) * w‖ + ‖a‖) =
      |2 * Complex.re (w * star a) + t * ‖w‖ ^ 2| := by
  have hmul :
      |‖a + (t : ℂ) * w‖ - ‖a‖| *
          (‖a + (t : ℂ) * w‖ + ‖a‖) =
        |2 * t * Complex.re (w * star a) + t ^ 2 * ‖w‖ ^ 2| := by
    have hnonneg : 0 <= ‖a + (t : ℂ) * w‖ + ‖a‖ := by positivity
    rw [← abs_of_nonneg hnonneg, ← abs_mul]
    have hsq := norm_sq_add_real_smul_wip a w t
    have hprod :
        (‖a + (t : ℂ) * w‖ - ‖a‖) *
            (‖a + (t : ℂ) * w‖ + ‖a‖) =
          2 * t * Complex.re (w * star a) + t ^ 2 * ‖w‖ ^ 2 := by linarith only [hsq]
    exact congrArg abs hprod
  have ht0 : t ≠ 0 := ne_of_gt ht
  calc
    |‖a + (t : ℂ) * w‖ - ‖a‖| / t *
        (‖a + (t : ℂ) * w‖ + ‖a‖)
        = (|‖a + (t : ℂ) * w‖ - ‖a‖| *
            (‖a + (t : ℂ) * w‖ + ‖a‖)) / t := by field_simp [ht0]
    _ = |2 * t * Complex.re (w * star a) + t ^ 2 * ‖w‖ ^ 2| / t := by rw [hmul]
    _ = |t * (2 * Complex.re (w * star a) + t * ‖w‖ ^ 2)| / t := by
          congr 1
          ring_nf
    _ = |t| * |2 * Complex.re (w * star a) + t * ‖w‖ ^ 2| / t := by rw [abs_mul]
    _ = |2 * Complex.re (w * star a) + t * ‖w‖ ^ 2| := by
          rw [abs_of_pos ht, mul_div_cancel_left₀ _ ht0]
private lemma continuous_defectFunctionPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Continuous (defectFunctionPkappa_coeff_wip kappa F G) := by
  unfold defectFunctionPkappa_coeff_wip
  exact (((continuous_evalPkappa_coeff_wip kappa (F + G)).norm.sub
    (continuous_evalPkappa_coeff_wip kappa F).norm).abs)
private theorem integrable_evalPkappa_sq_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.Integrable
      (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
  exact integrable_evalPkappa_sq hd kappa F
private theorem gaussianL2Norm_eq_lpNorm_coeff_wip
    {d : Nat} {α : Type*} [NormedAddCommGroup α]
     (F : Cd d -> α)
    (hF : MeasureTheory.AEStronglyMeasurable F (gammaD d)) :
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      MeasureTheory.lpNorm F 2 (gammaD d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := gammaD d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      MeasureTheory.lpNorm F (↑(2 : NNReal)) (gammaD d)
  rw [hlp]
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) ^ ((2 : ℝ)⁻¹)
  rw [Real.sqrt_eq_rpow]
  norm_num
private theorem memLp_two_defectFunctionPkappa_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    MeasureTheory.MemLp (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) := by
  let _ := hd
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (defectFunctionPkappa_coeff_wip kappa F G) (gammaD d) :=
    (continuous_defectFunctionPkappa_coeff_wip kappa F G).stronglyMeasurable.aestronglyMeasurable
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hplus_int :
      MeasureTheory.Integrable
        (fun z : Cd d => 2 * ‖evalPkappa kappa (F + G) z‖ ^ 2) (gammaD d) :=
    (integrable_evalPkappa_sq_coeff_wip hd kappa (F + G)).const_mul 2
  have hbase_int :
      MeasureTheory.Integrable
        (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) :=
    (integrable_evalPkappa_sq_coeff_wip hd kappa F).const_mul 2
  have hsq := hplus_int.add hbase_int
  have hmeasSq :
      MeasureTheory.AEStronglyMeasurable
        (fun z : Cd d => defectFunctionPkappa_coeff_wip kappa F G z ^ 2) (gammaD d) :=
    (continuous_defectFunctionPkappa_coeff_wip kappa F G).pow 2
      |>.stronglyMeasurable.aestronglyMeasurable
  have hbound :
      ∀ᵐ z ∂ gammaD d,
        ‖defectFunctionPkappa_coeff_wip kappa F G z ^ 2‖ <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
    filter_upwards with z
    have hsqz :
        defectFunctionPkappa_coeff_wip kappa F G z ^ 2 <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
      unfold defectFunctionPkappa_coeff_wip
      have : (‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖) ^ 2 <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
        linarith only [sq_nonneg (‖evalPkappa kappa (F + G) z‖ + ‖evalPkappa kappa F z‖)]
      simpa [sq_abs] using this
    simp_all
  simpa [Real.norm_eq_abs, abs_of_nonneg] using
    MeasureTheory.Integrable.mono' hsq hmeasSq hbound
private theorem defect_lpNorm_eq_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    defect F G =
      MeasureTheory.lpNorm (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) := by
  let _ := hd
  simpa [defect, defectFunctionPkappa_coeff_wip, Real.norm_eq_abs, sq_abs] using
    gaussianL2Norm_eq_lpNorm_coeff_wip (defectFunctionPkappa_coeff_wip kappa F G)
      (memLp_two_defectFunctionPkappa_coeff_wip hd kappa F G).aestronglyMeasurable
private theorem finite_head_bad_limit_eval_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa)
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ}
    {T : ℝ} {U : Skappa d kappa} {φ : ℕ -> ℕ}
    (ht_tendsto : Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
      Filter.atTop (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hpartial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (z : Cd d) :
    Filter.Tendsto
      (fun m => evalPkappa kappa (F + t (φ m) • H (φ m)) z)
      Filter.atTop
      (nhds (evalPkappa kappa F z + (T : ℂ) * toFun kappa U z)) := by
  exact evalPkappa_add_smul_tendsto_toFun_wip
    (kappa := kappa) F
    (H := fun m => H (φ m)) (U := U)
    (t := fun m => t (φ m)) (T := T)
    ht_tendsto hcoeff (fun m => hH_norm (φ m)) hpartial z
private theorem finite_head_bad_limit_defect_tendsto_zero_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa}
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_le : ∀ m, t m <= 4)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    Filter.Tendsto
      (fun m => defect F (t (φ m) • H (φ m)))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero
    (f := fun m => defect F (t (φ m) • H (φ m)))
    (g := fun m : ℕ => 4 * (1 / (((m + 1 : Nat) : ℝ))))
    (fun m => defect_nonneg_wip F (t (φ m) • H (φ m))) ?_ ?_
  · intro m
    have hφ_ge : m <= φ m := hφ_strict.id_le m
    have hden :
        (((m + 1 : Nat) : ℝ)) <= (((φ m + 1 : Nat) : ℝ)) := by exact_mod_cast Nat.succ_le_succ hφ_ge
    have hrecip :
        (1 / (((φ m + 1 : Nat) : ℝ))) <=
          (1 / (((m + 1 : Nat) : ℝ))) := one_div_le_one_div_of_le (by positivity) hden
    have hupper :
        (1 / (((φ m + 1 : Nat) : ℝ))) * t (φ m) <=
          4 * (1 / (((m + 1 : Nat) : ℝ))) := by
      calc
        (1 / (((φ m + 1 : Nat) : ℝ))) * t (φ m)
            <= (1 / (((φ m + 1 : Nat) : ℝ))) * 4 :=
              mul_le_mul_of_nonneg_left (ht_le (φ m)) (by positivity)
        _ <= (1 / (((m + 1 : Nat) : ℝ))) * 4 := mul_le_mul_of_nonneg_right hrecip (by norm_num)
        _ = 4 * (1 / (((m + 1 : Nat) : ℝ))) := by ring
    exact le_trans (le_of_lt (hdef (φ m))) hupper
  · have hbase :
        Filter.Tendsto
          (fun m : ℕ => (1 / (((m + 1 : Nat) : ℝ))))
          Filter.atTop (nhds 0) := by
      convert
        (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
          (fun m : ℕ => (1 / ((m : ℝ) + 1)))
          Filter.atTop (nhds 0)) using 1
      simp_all
    have hmul :
        Filter.Tendsto
          (fun m : ℕ => 4 * (1 / (((m + 1 : Nat) : ℝ))))
          Filter.atTop (nhds (4 * 0)) :=
      tendsto_const_nhds.mul hbase
    simpa using hmul
private theorem finite_head_bad_limit_defect_ae_tendsto_zero_wip
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    {F : Pkappa d kappa}
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_le : ∀ m, t m <= 4)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    ∃ ψ : ℕ -> ℕ, StrictMono ψ ∧
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m =>
            defectFunctionPkappa_coeff_wip kappa F
              (t (φ (ψ m)) • H (φ (ψ m))) z)
          Filter.atTop (nhds 0) := by
  let f : ℕ -> Cd d -> ℝ := fun m =>
    defectFunctionPkappa_coeff_wip kappa F (t (φ m) • H (φ m))
  have hdef_tendsto :
      Filter.Tendsto
        (fun m => defect F (t (φ m) • H (φ m)))
        Filter.atTop (nhds 0) :=
    finite_head_bad_limit_defect_tendsto_zero_wip hφ_strict ht_le hdef
  have hf_mem :
      ∀ m, MeasureTheory.MemLp (f m) 2 (gammaD d) := by
    intro m
    exact memLp_two_defectFunctionPkappa_coeff_wip hd kappa F
      (t (φ m) • H (φ m))
  have heLp_eq :
      ∀ m,
        MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d) =
          ENNReal.ofReal (defect F (t (φ m) • H (φ m))) := by
    intro m
    have hsub : (f m - fun _ : Cd d => (0 : ℝ)) = f m := by
      funext z
      simp
    rw [hsub,
      ← MeasureTheory.ofReal_lpNorm (hf_mem m),
      ← defect_lpNorm_eq_coeff_wip hd kappa F (t (φ m) • H (φ m))]
  have heLp_tendsto :
      Filter.Tendsto
        (fun m =>
          MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d))
        Filter.atTop (nhds 0) := by
    have hfun :
        (fun m =>
          MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d)) =
        fun m => ENNReal.ofReal (defect F (t (φ m) • H (φ m)) : ℝ) := by
      simp_all
    rw [hfun]
    simpa using ENNReal.tendsto_ofReal hdef_tendsto
  have hInMeasure :
      MeasureTheory.TendstoInMeasure (gammaD d) f Filter.atTop (fun _ : Cd d => (0 : ℝ)) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (p := (2 : ENNReal)) (μ := gammaD d)
      (f := f) (g := fun _ : Cd d => (0 : ℝ))
      (by norm_num) (fun m => (hf_mem m).aestronglyMeasurable) MeasureTheory.aestronglyMeasurable_const heLp_tendsto
  obtain ⟨ψ, hψ_strict, hψ_ae⟩ := hInMeasure.exists_seq_tendsto_ae
  refine ⟨ψ, hψ_strict, ?_⟩
  filter_upwards [hψ_ae] with z hz
  exact hz
private theorem finite_head_bad_limit_defect_quotient_ae_tendsto_zero_wip
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    {F : Pkappa d kappa}
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_pos : ∀ m, 0 < t m)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    ∃ ψ : ℕ -> ℕ, StrictMono ψ ∧
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m =>
            defectFunctionPkappa_coeff_wip kappa F
              (t (φ (ψ m)) • H (φ (ψ m))) z / t (φ (ψ m)))
          Filter.atTop (nhds 0) := by
  let f : ℕ -> Cd d -> ℝ := fun m z =>
    defectFunctionPkappa_coeff_wip kappa F (t (φ m) • H (φ m)) z / t (φ m)
  have hf_eq :
      ∀ m,
        f m =
          ((t (φ m))⁻¹ : ℝ) •
            defectFunctionPkappa_coeff_wip kappa F (t (φ m) • H (φ m)) := by
    intro m
    funext z
    simp [f, Pi.smul_apply, div_eq_mul_inv, mul_comm]
  have hf_mem :
      ∀ m, MeasureTheory.MemLp (f m) 2 (gammaD d) := by
    intro m
    rw [hf_eq m]
    exact (memLp_two_defectFunctionPkappa_coeff_wip hd kappa F
      (t (φ m) • H (φ m))).const_smul ((t (φ m))⁻¹ : ℝ)
  have hbound :
      ∀ m,
        MeasureTheory.eLpNorm (f m) 2 (gammaD d) <=
          ENNReal.ofReal (1 / ((m + 1 : Nat) : ℝ)) := by
    intro m
    have hf_mem_m := hf_mem m
    have hfin : MeasureTheory.eLpNorm (f m) 2 (gammaD d) ≠ ⊤ := hf_mem_m.eLpNorm_ne_top
    refine (ENNReal.le_ofReal_iff_toReal_le hfin (by positivity)).2 ?_
    rw [MeasureTheory.toReal_eLpNorm hf_mem_m.aestronglyMeasurable, hf_eq m,
      MeasureTheory.lpNorm_const_smul]
    rw [← defect_lpNorm_eq_coeff_wip hd kappa F (t (φ m) • H (φ m))]
    have hratio :
        defect F (t (φ m) • H (φ m)) / t (φ m) <
          1 / (((φ m + 1 : Nat) : ℝ)) := by
      have hdiv :=
        div_lt_div_of_pos_right (hdef (φ m)) (ht_pos (φ m))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        (ht_pos (φ m)).ne'] using hdiv
    have hφ_ge : m <= φ m := hφ_strict.id_le m
    have hden :
        (((m + 1 : Nat) : ℝ)) <= (((φ m + 1 : Nat) : ℝ)) := by exact_mod_cast Nat.succ_le_succ hφ_ge
    have hfinal :
        defect F (t (φ m) • H (φ m)) / t (φ m) <=
          1 / (((m + 1 : Nat) : ℝ)) := (le_of_lt hratio).trans
        (one_div_le_one_div_of_le (by positivity) hden)
    simpa [Real.norm_eq_abs, abs_of_pos (ht_pos (φ m)), div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hfinal
  have htarget :
      Filter.Tendsto
        (fun m : ℕ => ENNReal.ofReal (1 / ((m + 1 : Nat) : ℝ)))
        Filter.atTop (nhds 0) := by
    have hbase :
        Filter.Tendsto
          (fun m : ℕ => (1 / ((m + 1 : Nat) : ℝ)))
          Filter.atTop (nhds 0) := by
      convert
        (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
          (fun m : ℕ => (1 / ((m : ℝ) + 1)))
          Filter.atTop (nhds 0)) using 1
      simp_all
    simpa using ENNReal.tendsto_ofReal hbase
  have heLp_tendsto :
      Filter.Tendsto
        (fun m =>
          MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d))
        Filter.atTop (nhds 0) := by
    have hfun :
        (fun m =>
          MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d)) =
        fun m => MeasureTheory.eLpNorm (f m) 2 (gammaD d) := by
      funext m
      congr 1
      funext z
      simp
    rw [hfun, ENNReal.tendsto_nhds_zero]
    intro eps heps
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp htarget) eps heps] with m hm
    exact le_trans (hbound m) hm
  have hInMeasure :
      MeasureTheory.TendstoInMeasure (gammaD d) f Filter.atTop (fun _ : Cd d => (0 : ℝ)) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (p := (2 : ENNReal)) (μ := gammaD d)
      (f := f) (g := fun _ : Cd d => (0 : ℝ))
      (by norm_num) (fun m => (hf_mem m).aestronglyMeasurable) MeasureTheory.aestronglyMeasurable_const heLp_tendsto
  obtain ⟨ψ, hψ_strict, hψ_ae⟩ := hInMeasure.exists_seq_tendsto_ae
  refine ⟨ψ, hψ_strict, ?_⟩
  filter_upwards [hψ_ae] with z hz
  exact hz
private theorem finite_head_bad_limit_real_part_ae_wip
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (F : Pkappa d kappa)
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ}
    {U : Skappa d kappa} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_tendsto_zero :
      Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds 0))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
      Filter.atTop (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hpartial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (ht_pos : ∀ m, 0 < t m)
    (ht_le : ∀ m, t m <= 4)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    (fun z => Complex.re (toFun kappa U z * star (evalPkappa kappa F z)))
      =ᵐ[gammaD d] fun _ => 0 := by
  obtain ⟨ψ, hψ_strict, hquot_ae⟩ :=
    finite_head_bad_limit_defect_quotient_ae_tendsto_zero_wip
      (hd := hd) (kappa := kappa) (F := F) (H := H) (t := t) (φ := φ)
      hφ_strict ht_pos hdef
  have ht_sub_tendsto_zero :
      Filter.Tendsto (fun m => t (φ (ψ m))) Filter.atTop (nhds 0) :=
    ht_tendsto_zero.comp hψ_strict.tendsto_atTop
  have hpointwise :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m => evalPkappa kappa (H (φ (ψ m))) z)
          Filter.atTop
          (nhds (toFun kappa U z)) := by
    filter_upwards with z
    have hz :=
      evalPkappa_tendsto_toFun_of_coeff_tendsto_wip
        (kappa := kappa) (H := fun m => H (φ m)) (U := U)
        hcoeff (fun m => hH_norm (φ m)) hpartial z
    exact hz.comp hψ_strict.tendsto_atTop
  have hreal :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m =>
            Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
              star (evalPkappa kappa F z)))
          Filter.atTop (nhds 0) := by
    filter_upwards [hquot_ae] with z hzquot
    let Cz : ℝ := Real.sqrt (∑' alpha : Idx d, ‖Phi kappa alpha z‖ ^ 2)
    have hCz_nn : 0 <= Cz := by
      dsimp [Cz]
      exact Real.sqrt_nonneg _
    have hw_bound :
        ∀ m : ℕ, ‖evalPkappa kappa (H (φ (ψ m))) z‖ <= Cz := by
      intro m
      exact evalPkappa_norm_le_kernel_sqrt_wip kappa (H (φ (ψ m)))
        (hH_norm (φ (ψ m))) z
    have hR_nonneg :
        ∀ m : ℕ,
          0 <=
            defectFunctionPkappa_coeff_wip kappa F
              (t (φ (ψ m)) • H (φ (ψ m))) z / t (φ (ψ m)) := by
      intro m
      exact div_nonneg (abs_nonneg _) (le_of_lt (ht_pos (φ (ψ m))))
    have hlin_eq :
        ∀ m : ℕ,
          defectFunctionPkappa_coeff_wip kappa F
              (t (φ (ψ m)) • H (φ (ψ m))) z / t (φ (ψ m)) *
              (‖evalPkappa kappa F z +
                  (t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖ +
                ‖evalPkappa kappa F z‖) =
            |2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
                  star (evalPkappa kappa F z)) +
                t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2| := by
      intro m
      simpa [defectFunctionPkappa_coeff_wip, evalPkappa_add_apply_wip,
        evalPkappa_smul_real_wip] using
        (defectFunction_div_eq_abs_linearization_wip
          (evalPkappa kappa F z)
          (evalPkappa kappa (H (φ (ψ m))) z)
          (ht_pos (φ (ψ m))))
    have hfactor_bound :
        ∀ m : ℕ,
          ‖evalPkappa kappa F z +
              (t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖ +
              ‖evalPkappa kappa F z‖ <=
            2 * ‖evalPkappa kappa F z‖ + 4 * Cz := by
      intro m
      have htm_nonneg : 0 <= t (φ (ψ m)) := le_of_lt (ht_pos (φ (ψ m)))
      calc
        ‖evalPkappa kappa F z +
            (t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖ +
            ‖evalPkappa kappa F z‖
            <= (‖evalPkappa kappa F z‖ +
                ‖(t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖) +
                ‖evalPkappa kappa F z‖ := by
              gcongr
              exact norm_add_le _ _
        _ = 2 * ‖evalPkappa kappa F z‖ +
              ‖(t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖ := by ring_nf
        _ = 2 * ‖evalPkappa kappa F z‖ +
              t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htm_nonneg]
        _ <= 2 * ‖evalPkappa kappa F z‖ +
              4 * ‖evalPkappa kappa (H (φ (ψ m))) z‖ := by
              gcongr
              exact ht_le (φ (ψ m))
        _ <= 2 * ‖evalPkappa kappa F z‖ + 4 * Cz := by
              simp_all
    have hprod :
        Filter.Tendsto
          (fun m =>
            (defectFunctionPkappa_coeff_wip kappa F
                (t (φ (ψ m)) • H (φ (ψ m))) z / t (φ (ψ m))) *
              (2 * ‖evalPkappa kappa F z‖ + 4 * Cz))
          Filter.atTop (nhds 0) := by simpa using hzquot.mul tendsto_const_nhds
    have habs :
        Filter.Tendsto
          (fun m =>
            |2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
                  star (evalPkappa kappa F z)) +
                t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2|)
          Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun m => abs_nonneg _) ?_ hprod
      intro m
      rw [← hlin_eq m]
      exact mul_le_mul_of_nonneg_left (hfactor_bound m) (hR_nonneg m)
    have hlin :
        Filter.Tendsto
          (fun m =>
            2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
                  star (evalPkappa kappa F z)) +
                t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2)
          Filter.atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).2 habs
    have herror :
        Filter.Tendsto
          (fun m =>
            t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2)
          Filter.atTop (nhds 0) := by
      have hbound_err :
          ∀ m : ℕ,
            t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2 <=
              (Cz ^ 2) * t (φ (ψ m)) := by
        intro m
        have hsq :
            ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2 <= Cz ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hCz_nn).2 (hw_bound m)
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hsq (le_of_lt (ht_pos (φ (ψ m))))
      have hczsq :
          Filter.Tendsto (fun m => (Cz ^ 2) * t (φ (ψ m))) Filter.atTop (nhds 0) := by
        have htmp :
            Filter.Tendsto (fun m => (Cz ^ 2) * t (φ (ψ m)))
              Filter.atTop (nhds ((Cz ^ 2) * 0)) :=
          tendsto_const_nhds.mul ht_sub_tendsto_zero
        simpa using htmp
      refine squeeze_zero
        (fun m => mul_nonneg (le_of_lt (ht_pos (φ (ψ m)))) (sq_nonneg _))
        hbound_err hczsq
    have htwo :
        Filter.Tendsto
          (fun m =>
            2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
              star (evalPkappa kappa F z)))
          Filter.atTop (nhds 0) := by
      have hsub := hlin.sub herror
      simp_all
    have hhalf :
        Filter.Tendsto
          (fun m =>
            (1 / 2 : ℝ) *
              (2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
                star (evalPkappa kappa F z))))
          Filter.atTop (nhds ((1 / 2 : ℝ) * 0)) :=
      tendsto_const_nhds.mul htwo
    simp_all
  exact
    ae_real_part_eq_zero_of_tendsto_wip
      (base := evalPkappa kappa F)
      (u := fun m z => evalPkappa kappa (H (φ (ψ m))) z)
      (limit := toFun kappa U)
      hpointwise hreal
private theorem finite_head_bad_limit_modulus_ae_wip
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (F : Pkappa d kappa)
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ}
    {T : ℝ} {U : Skappa d kappa} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_tendsto : Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
      Filter.atTop (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hpartial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (ht_le : ∀ m, t m <= 4)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    (fun z => ‖evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
      =ᵐ[gammaD d] fun z => ‖evalPkappa kappa F z‖ := by
  obtain ⟨ψ, hψ_strict, hdef_ae⟩ :=
    finite_head_bad_limit_defect_ae_tendsto_zero_wip
      (hd := hd) (kappa := kappa) (F := F) (H := H) (t := t) (φ := φ)
      hφ_strict ht_le hdef
  have hpointwise :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m => evalPkappa kappa (F + t (φ (ψ m)) • H (φ (ψ m))) z)
          Filter.atTop
          (nhds (evalPkappa kappa F z + (T : ℂ) * toFun kappa U z)) := by
    filter_upwards with z
    have hz :=
      finite_head_bad_limit_eval_tendsto_wip
        (kappa := kappa) F ht_tendsto hcoeff hH_norm hpartial z
    exact hz.comp hψ_strict.tendsto_atTop
  have hdefect :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m =>
            |‖evalPkappa kappa (F + t (φ (ψ m)) • H (φ (ψ m))) z‖ -
              ‖evalPkappa kappa F z‖|)
          Filter.atTop (nhds 0) := by
    filter_upwards [hdef_ae] with z hz
    exact hz
  exact ae_norm_eq_of_tendsto_defect_wip hpointwise hdefect
private theorem coeff_skappaAffinePkappa_wip
    {d : Nat} (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa) (a b : ℂ) (alpha : Idx d) :
    coeffSkappa (skappaAffinePkappa_wip kappa F U a b) alpha =
      a * coeffPkappa F alpha + b * coeffSkappa U alpha := by rfl
private theorem toFun_skappaAffinePkappa_wip
    {d : Nat} (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa) (a b : ℂ) :
    toFun kappa (skappaAffinePkappa_wip kappa F U a b) =
      fun z => a * evalPkappa kappa F z + b * toFun kappa U z := by
  ext z
  have hFsum := summable_pkappa_eval_mul_wip kappa F z
  have hUsum := summable_skappa_eval_mul_wip kappa U z
  have hFsum' :
      Summable (fun alpha : Idx d => a * (coeffPkappa F alpha * Phi kappa alpha z)) :=
    hFsum.mul_left a
  have hUsum' :
      Summable (fun alpha : Idx d => b * (coeffSkappa U alpha * Phi kappa alpha z)) :=
    hUsum.mul_left b
  unfold toFun
  calc
    ∑' alpha : Idx d,
        coeffSkappa (skappaAffinePkappa_wip kappa F U a b) alpha * Phi kappa alpha z
        = (∑' alpha : Idx d,
            (a * (coeffPkappa F alpha * Phi kappa alpha z) +
              b * (coeffSkappa U alpha * Phi kappa alpha z))) := tsum_congr fun alpha => by
            change
              (a * coeffPkappa F alpha + b * coeffSkappa U alpha) *
                  Phi kappa alpha z =
                a * (coeffPkappa F alpha * Phi kappa alpha z) +
                  b * (coeffSkappa U alpha * Phi kappa alpha z)
            ring
    _ = (∑' alpha : Idx d, a * (coeffPkappa F alpha * Phi kappa alpha z)) +
          ∑' alpha : Idx d, b * (coeffSkappa U alpha * Phi kappa alpha z) := hFsum'.tsum_add hUsum'
    _ = a * (∑' alpha : Idx d, coeffPkappa F alpha * Phi kappa alpha z) +
          b * (∑' alpha : Idx d, coeffSkappa U alpha * Phi kappa alpha z) := by
          rw [hFsum.tsum_mul_left, hUsum.tsum_mul_left]
    _ = a * evalPkappa kappa F z + b * (∑' alpha : Idx d,
          coeffSkappa U alpha * Phi kappa alpha z) := by rw [evalPkappa_eq_tsum_coeff_wip kappa F z]
private theorem skappa_exact_modulus_affine_relation_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa)
    (a b c e : ℂ)
    (hmod :
      (fun z => ‖c * evalPkappa kappa F z + e * toFun kappa U z‖)
        =ᵐ[gammaD d]
      fun z => ‖a * evalPkappa kappa F z + b * toFun kappa U z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ∀ alpha,
        c * coeffPkappa F alpha + e * coeffSkappa U alpha =
          w * (a * coeffPkappa F alpha + b * coeffSkappa U alpha) := by
  let X : Skappa d kappa := skappaAffinePkappa_wip kappa F U a b
  let Y : Skappa d kappa := skappaAffinePkappa_wip kappa F U c e
  have hmodXY :
      (fun z => ‖toFun kappa X z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa Y z‖ := by
    filter_upwards [hmod] with z hz
    simpa [X, Y, toFun_skappaAffinePkappa_wip] using hz.symm
  obtain ⟨w, hw, hYX⟩ :=
    exact_modulus_recovery_skappa_ae hd kappa hmodXY
  refine ⟨w, hw, ?_⟩
  intro alpha
  have hcoeff := congrArg (fun S : Skappa d kappa => coeffSkappa S alpha) hYX
  simp only [X, Y] at hcoeff
  have hsmul :
      coeffSkappa (w • skappaAffinePkappa_wip kappa F U a b) alpha
        = w * coeffSkappa (skappaAffinePkappa_wip kappa F U a b) alpha := rfl
  rw [coeff_skappaAffinePkappa_wip, hsmul, coeff_skappaAffinePkappa_wip] at hcoeff
  exact hcoeff
private theorem skappa_modulus_phase_relation_against_pkappa_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0)
    {T : ℝ} (hT_pos : 0 < T) (U : Skappa d kappa)
    (hmod :
      (fun z => ‖evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
        =ᵐ[gammaD d] fun z => ‖evalPkappa kappa F z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ∀ alpha,
        coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha =
          w * coeffPkappa F alpha := by
  let _ := hF_ne
  let _ := hT_pos
  have hmod' :
      (fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
        =ᵐ[gammaD d]
      fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (0 : ℂ) * toFun kappa U z‖ := by
    simp_all
  obtain ⟨w, hw, hrel⟩ :=
    skappa_exact_modulus_affine_relation_wip
      hd kappa F U (1 : ℂ) (0 : ℂ) (1 : ℂ) (T : ℂ) hmod'
  refine ⟨w, hw, ?_⟩
  simp_all
private theorem skappa_real_part_scalar_relation_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (U : Skappa d kappa)
    (hreal :
      (fun z => Complex.re (toFun kappa U z * star (evalPkappa kappa F z)))
        =ᵐ[gammaD d] fun _ => 0) :
    ∃ c : ℂ, ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha := by
  have hmod :
      (fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (1 : ℂ) * toFun kappa U z‖)
        =ᵐ[gammaD d]
      fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (-1 : ℂ) * toFun kappa U z‖ := by
    filter_upwards [hreal] with z hz
    let f : ℂ := evalPkappa kappa F z
    let u : ℂ := toFun kappa U z
    have hsq :
        ‖f + u‖ ^ 2 = ‖f + (-1 : ℂ) * u‖ ^ 2 := by
      have hplus := norm_sq_add_real_smul_wip f u 1
      have hminus := norm_sq_add_real_smul_wip f u (-1)
      have hplus' :
          ‖f + u‖ ^ 2 =
            ‖f‖ ^ 2 + 1 ^ 2 * ‖u‖ ^ 2 + 2 * 1 * Complex.re (u * star f) := by simpa using hplus
      have hminus' :
          ‖f + (-1 : ℂ) * u‖ ^ 2 =
            ‖f‖ ^ 2 + (-1 : ℝ) ^ 2 * ‖u‖ ^ 2 +
              2 * (-1 : ℝ) * Complex.re (u * star f) := by simpa using hminus
      have hz' : Complex.re (u * star f) = 0 := by simpa [f, u] using hz
      linarith only [hz, hplus', hminus']
    have hnorm : ‖f + u‖ = ‖f + (-1 : ℂ) * u‖ := by
      simp_all
    simpa [f, u] using hnorm
  obtain ⟨w, hw, hrel⟩ :=
    skappa_exact_modulus_affine_relation_wip
      hd kappa F U (1 : ℂ) (-1 : ℂ) (1 : ℂ) (1 : ℂ) hmod
  by_cases hw_neg : w = -1
  · exfalso
    apply hF_ne
    ext alpha
    have h :
        coeffPkappa F alpha + coeffSkappa U alpha =
          w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) := by simpa using hrel alpha
    rw [hw_neg] at h
    have htwo :
        (2 : ℂ) * coeffPkappa F alpha = 0 := by
      calc
        (2 : ℂ) * coeffPkappa F alpha
            =
              (coeffPkappa F alpha + coeffSkappa U alpha) -
                ((-1 : ℂ) *
                  (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha)) := by ring
        _ = 0 := by rw [h]; ring
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  · have hw_add_ne : (1 : ℂ) + w ≠ 0 := by
      intro hsum
      apply hw_neg
      have hsum' : w + 1 = 0 := by simpa [add_comm] using hsum
      exact eq_neg_iff_add_eq_zero.mpr hsum'
    let c : ℂ := (w - 1) / ((1 : ℂ) + w)
    refine ⟨c, ?_⟩
    intro alpha
    have h :
        coeffPkappa F alpha + coeffSkappa U alpha =
          w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) := by simpa using hrel alpha
    have hlin :
        ((1 : ℂ) + w) * coeffSkappa U alpha =
          (w - 1) * coeffPkappa F alpha := by
      calc
        ((1 : ℂ) + w) * coeffSkappa U alpha
            =
              (coeffPkappa F alpha + coeffSkappa U alpha) +
                w * coeffSkappa U alpha - coeffPkappa F alpha := by ring
        _ =
              w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) +
                w * coeffSkappa U alpha - coeffPkappa F alpha := by rw [h]
        _ = (w - 1) * coeffPkappa F alpha := by ring
    calc
      coeffSkappa U alpha
          = (((1 : ℂ) + w)⁻¹) * (((1 : ℂ) + w) * coeffSkappa U alpha) := by field_simp [hw_add_ne]
      _ = (((1 : ℂ) + w)⁻¹) * ((w - 1) * coeffPkappa F alpha) := by rw [hlin]
      _ = c * coeffPkappa F alpha := by
            dsimp [c]
            field_simp [hw_add_ne]
private theorem coeff_zero_of_modulus_phase_relation_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {T : ℝ} (hT_pos : 0 < T) {U : Skappa d kappa} {w : ℂ}
    (hrel : ∀ alpha,
      coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha =
        w * coeffPkappa F alpha)
    (horth : orthogonalToSkappa_wip F U) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  have hT_ne : (T : ℂ) ≠ 0 := by exact_mod_cast hT_pos.ne'
  have hcoeff :
      ∀ alpha,
        coeffSkappa U alpha =
          (((T : ℂ)⁻¹ * (w - 1)) * coeffPkappa F alpha) := by
    intro alpha
    have hTU :
        (T : ℂ) * coeffSkappa U alpha =
          (w - 1) * coeffPkappa F alpha := by
      calc
        (T : ℂ) * coeffSkappa U alpha
            = (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) -
                coeffPkappa F alpha := by ring
        _ = w * coeffPkappa F alpha - coeffPkappa F alpha := by rw [hrel alpha]
        _ = (w - 1) * coeffPkappa F alpha := by ring
    calc
      coeffSkappa U alpha
          = (T : ℂ)⁻¹ * ((T : ℂ) * coeffSkappa U alpha) := by field_simp [hT_ne]
      _ = (T : ℂ)⁻¹ * ((w - 1) * coeffPkappa F alpha) := by rw [hTU]
      _ = (((T : ℂ)⁻¹ * (w - 1)) * coeffPkappa F alpha) := by ring
  exact coeff_zero_of_scalar_multiple_orthogonalToSkappa_wip hF_norm hcoeff horth
private theorem coeff_zero_of_real_part_scalar_relation_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {U : Skappa d kappa} {c : ℂ}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha)
    (horth : orthogonalToSkappa_wip F U) :
    ∀ alpha, coeffSkappa U alpha = 0 :=
  coeff_zero_of_scalar_multiple_orthogonalToSkappa_wip hF_norm hcoeff horth
private theorem bad_limit_coeff_zero_from_exact_rigidity_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    {T : ℝ} {U : Skappa d kappa}
    (hT_mem : T ∈ Set.Icc (0 : ℝ) 4)
    (horth : orthogonalToSkappa_wip F U)
    (hreal :
      T = 0 ->
        (fun z => Complex.re (toFun kappa U z * star (evalPkappa kappa F z)))
          =ᵐ[gammaD d] fun _ => 0)
    (hmod :
      0 < T ->
        (fun z => ‖evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
          =ᵐ[gammaD d] fun z => ‖evalPkappa kappa F z‖) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  by_cases hT_zero : T = 0
  · obtain ⟨c, hc⟩ :=
      skappa_real_part_scalar_relation_wip hd kappa F hF_ne U (hreal hT_zero)
    exact coeff_zero_of_real_part_scalar_relation_wip hF_norm hc horth
  · have hT_pos : 0 < T := lt_of_le_of_ne hT_mem.1 (Ne.symm hT_zero)
    obtain ⟨w, hw, hrel⟩ :=
      skappa_modulus_phase_relation_against_pkappa_wip
        hd kappa F hF_ne hT_pos U (hmod hT_pos)
    exact coeff_zero_of_modulus_phase_relation_wip hF_norm hT_pos hrel horth
private theorem finite_head_defect_lower_bound_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    (K : Finset (Idx d)) (rho : ℝ) (h_rho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
        0 < t ->
        t <= 4 ->
        delta * t <= defect F (t • H) := by
  by_contra hbad
  obtain
    ⟨H, t, T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial,
      hmass_U, horth, hH_norm, hmass, ht_pos, ht_le, hdef, horth_U⟩ :=
    finite_head_bad_limit_data_wip F K (rho := rho) hbad
  have hzero : ∀ alpha, coeffSkappa U alpha = 0 := by
    refine
      bad_limit_coeff_zero_from_exact_rigidity_wip
        hd kappa F hF_ne hF_norm hT_mem horth_U ?_ ?_
    · intro hT_zero
      have ht_tendsto_zero :
          Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds 0) := by
        simpa [hT_zero] using ht_tendsto
      exact
        finite_head_bad_limit_real_part_ae_wip
          (hd := hd) (kappa := kappa) F hφ_strict ht_tendsto_zero
          hcoeff hH_norm hpartial ht_pos ht_le hdef
    · intro hT_pos
      exact
        finite_head_bad_limit_modulus_ae_wip
          (hd := hd) (kappa := kappa) F hφ_strict ht_tendsto
          hcoeff hH_norm hpartial ht_le hdef
  exact finite_head_mass_contradiction_of_coeff_zero_wip K h_rho hmass_U hzero
private theorem coefficient_head_mass_of_highAnnulus_small_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (E : Finset (Idx d)) (J : Nat) :
    ∃ Kextra : Finset (Idx d), ∃ rho_head : ℝ, 0 < rho_head ∧
      ∀ {H : Pkappa d kappa},
        ‖H‖ = 1 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        rho_head <=
          Finset.sum (coefficientControlSet_wip E F ∪ Kextra)
            (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
  obtain ⟨Kextra, rho_head, hrho_head_pos, hlow⟩ :=
    lowAnnulusProjection hd kappa J
  refine ⟨Kextra, rho_head, hrho_head_pos, ?_⟩
  intro H hH_norm hhigh
  have hpartition := annulusMassPartition hd kappa J H
  have hH_sq : ‖H‖ ^ 2 = 1 := by nlinarith only [hH_norm]
  have hlow_lower : 1 / 4 < lowAnnulusMass J (ofPkappa kappa H) := by
    linarith only [
      hhigh, hpartition, hH_sq
    ]
  have hKextra_mass_gt :
      rho_head < Finset.sum Kextra (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    by_contra hnot
    have hmass_le :
        Finset.sum Kextra (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <= rho_head :=
      le_of_not_gt hnot
    have hlow_upper : lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 :=
      hlow hH_norm hmass_le
    linarith only [hhigh, hpartition, hH_sq, hlow_upper]
  have hKextra_subset : Kextra ⊆ coefficientControlSet_wip E F ∪ Kextra := by
    simp_all
  have hsum_le_union :
      Finset.sum Kextra (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <=
        Finset.sum (coefficientControlSet_wip E F ∪ Kextra)
          (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hKextra_subset
      (by intro alpha halpha hnot; positivity)
  exact le_trans (le_of_lt hKextra_mass_gt) hsum_le_union
private theorem lowAnnulusDefectControl_of_finite_head_lower_bound_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (J : Nat)
    (hhead_lower :
      ∀ (K : Finset (Idx d)) (rho : ℝ), 0 < rho ->
        ∃ delta : ℝ, 0 < delta ∧
          ∀ {H : Pkappa d kappa} {t : ℝ},
            orthogonalToPk F H ->
            ‖H‖ = 1 ->
            rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
            0 < t ->
            t <= 4 ->
            delta * t <= defect F (t • H)) :
    ∃ delta_low : ℝ, 0 < delta_low ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        defect F (t • H) <= delta_low * t ->
        lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  let E0 : Finset (Idx d) := ∅
  obtain ⟨Kextra, rho_head, hrho_head_pos, hhead⟩ :=
    coefficient_head_mass_of_highAnnulus_small_wip hd kappa F E0 J
  let K : Finset (Idx d) := coefficientControlSet_wip E0 F ∪ Kextra
  obtain ⟨delta_head, hdelta_head_pos, hdefect_lower⟩ :=
    hhead_lower K rho_head hrho_head_pos
  refine ⟨delta_head / 2, by positivity, ?_⟩
  intro H t horth hH_norm ht_pos ht_le_four hhigh hdefect
  have hmass :
      rho_head <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    dsimp [K]
    exact hhead hH_norm hhigh
  have hlower : delta_head * t <= defect F (t • H) :=
    hdefect_lower horth hH_norm hmass ht_pos ht_le_four
  have hupper : defect F (t • H) <= (delta_head / 2) * t := hdefect
  exfalso
  nlinarith only [hdelta_head_pos, ht_pos, hlower, hupper]
private theorem finite_window_lowAnnulusDefectControl_core_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    (J : Nat) :
    ∃ delta_low : ℝ, 0 < delta_low ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        defect F (t • H) <= delta_low * t ->
        lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  exact
    lowAnnulusDefectControl_of_finite_head_lower_bound_wip hd kappa F J
      (fun K rho h_rho =>
        finite_head_defect_lower_bound_wip hd kappa F hF_ne hF_norm K rho h_rho)
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    (J : Nat) :
    ∃ delta_low : ℝ, 0 < delta_low ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        defect F (t • H) <= delta_low * t ->
        lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  let _ := hd
  let _ := hF_ne
  let _ := hF_norm
  /-
  Assembly-specific compactness/no-escape output:
  small defect, after the high-annulus estimate has localized the normalized
  perturbation, must force the low-annulus mass small. This is weaker than the
  previous arbitrary finite-coefficient statement and is exactly the bridge used
  by `orthogonal_coercivity`.
  -/
  by_cases hJ : J = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro H t horth hH_norm ht_pos ht_le_four hhigh hdefect
    subst J
    have hnonempty : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    have hempty : lowAnnuli d 0 = ∅ := by simp [lowAnnuli]
    simp [lowAnnulusMass, hempty]
  · exact finite_window_lowAnnulusDefectControl_core_wip hd kappa F hF_ne hF_norm J
end DimdPolyLEAN
