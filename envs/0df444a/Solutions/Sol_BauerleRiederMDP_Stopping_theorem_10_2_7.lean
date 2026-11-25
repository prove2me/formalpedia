-- Prove2me | solution 1 for BauerleRiederMDP.Stopping.theorem_10_2_7
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T20:38:40.99779+00:00
-- url     : https://prove2.me/submissions/6fcb943b-c336-47a4-a561-d232527dabee

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary
import Definitions.Def_BauerleRiederMDP_Stopping_lookAheadSet
import Definitions.Def_BauerleRiederMDP_Stopping_IsOptimalUpTo
import Definitions.Def_BauerleRiederMDP_Stopping_AssumptionBLim
import Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_2_2
import Theorems.Thm_BauerleRiederMDP_Stopping_theorem_10_1_5

open MeasureTheory Filter Topology
open MDPFinance.OptimalStopping

namespace MDPS1027

variable {E : Type*} [MeasurableSpace E]

lemma erealIntegral_mono {α : Type*} [MeasurableSpace α] (μ : Measure α) {v w : α → EReal}
    (h : ∀ x, v x ≤ w x) : erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  refine add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _))) ?_
  exact EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (lintegral_mono fun x => EReal.toENNReal_le_toENNReal
      (sup_le_sup_right (EReal.neg_le_neg_iff.2 (h x)) _)))

lemma measurable_erealIntegral (Q : E → Measure E) (hQ : Measurable Q) {v : E → EReal}
    (hv : Measurable v) : Measurable fun x => erealIntegral (Q x) v := by
  unfold erealIntegral
  have h1 : Measurable fun y => (v y ⊔ 0).toENNReal := (hv.sup measurable_const).ereal_toENNReal
  have h2 : Measurable fun y => ((-v y) ⊔ 0).toENNReal :=
    ((continuous_neg.measurable.comp hv).sup measurable_const).ereal_toENNReal
  have k1 := (Measure.measurable_lintegral h1).comp hQ
  have k2 := (Measure.measurable_lintegral h2).comp hQ
  exact (measurable_coe_ennreal_ereal.comp k1).add
    (continuous_neg.measurable.comp (measurable_coe_ennreal_ereal.comp k2))

lemma beta_nonneg (P : StationaryProblem E) : (0 : EReal) ≤ (P.beta : EReal) := by
  exact_mod_cast P.beta_mem.1.le

lemma T_mono (P : StationaryProblem E) {v w : E → EReal} (h : ∀ x, v x ≤ w x) (x : E) :
    P.T v x ≤ P.T w x := by
  unfold StationaryProblem.T
  exact max_le_max le_rfl (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (erealIntegral_mono _ h) (beta_nonneg P)))

lemma g_le_T (P : StationaryProblem E) (v : E → EReal) (x : E) : (P.g x : EReal) ≤ P.T v x :=
  le_max_left _ _

lemma J_succ_mono (P : StationaryProblem E) (n : ℕ) (x : E) : P.J n x ≤ P.J (n + 1) x := by
  induction n generalizing x with
  | zero => exact g_le_T P _ x
  | succ n ih => exact T_mono P ih x

lemma J_mono (P : StationaryProblem E) (x : E) : Monotone fun n => P.J n x :=
  monotone_nat_of_le_succ fun n => J_succ_mono P n x

lemma g_le_J (P : StationaryProblem E) (n : ℕ) (x : E) : (P.g x : EReal) ≤ P.J n x :=
  J_mono P x (Nat.zero_le n)

lemma J_le_Jlim (P : StationaryProblem E) (n : ℕ) (x : E) : P.J n x ≤ P.Jlim x :=
  le_iSup (fun n => P.J n x) n

lemma J_measurable (P : StationaryProblem E) (n : ℕ) : Measurable (P.J n) := by
  induction n with
  | zero => exact measurable_coe_real_ereal.comp P.g_meas
  | succ n ih =>
    change Measurable fun x => max (P.g x : EReal)
      ((P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) (P.J n))
    exact (measurable_coe_real_ereal.comp P.g_meas).max
      ((measurable_coe_real_ereal.comp P.c_meas).add
        ((measurable_erealIntegral P.QX P.QX_meas ih).const_mul _))

lemma hitTime_le_iff (S : Set E) (w : ℕ → E) (n : ℕ) :
    hitTime S w ≤ (n : ℕ∞) ↔ ∃ k ≤ n, w k ∈ S := by
  unfold hitTime
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : ((n + 1 : ℕ) : ℕ∞) ≤ sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S}) := by
      refine le_sInf ?_
      rintro _ ⟨k, hk, rfl⟩
      have : ¬ k ≤ n := fun hkn => hc k hkn hk
      show ((n + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)
      exact_mod_cast (by omega : n + 1 ≤ k)
    have := this.trans h
    have : n + 1 ≤ n := by exact_mod_cast this
    omega
  · rintro ⟨k, hk, hS⟩
    have hmem : (k : ℕ∞) ∈ (fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S} := ⟨k, hS, rfl⟩
    exact (sInf_le hmem).trans (by exact_mod_cast hk)

lemma isStopTime_hitTime {S : Set E} (hS : MeasurableSet S) : IsStopTime (hitTime S) := by
  intro n
  have : {w : ℕ → E | hitTime S w ≤ (n : ℕ∞)} =
      (fun w : ℕ → E => fun i : Fin (n + 1) => w i) ⁻¹'
        (⋃ k : Fin (n + 1), {f : Fin (n + 1) → E | f k ∈ S}) := by
    ext w
    simp only [Set.mem_ofPred_eq, hitTime_le_iff, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨⟨k, by omega⟩, h⟩
    · rintro ⟨k, h⟩; exact ⟨k, by omega, h⟩
  rw [this]
  exact MeasurableSet.preimage (MeasurableSet.iUnion fun k => measurable_pi_apply k hS)
    (comap_measurable _)

open BauerleRiederMDP.Stopping

lemma erealIntegral_congr_ae {α : Type*} [MeasurableSpace α] (μ : Measure α) {v w : α → EReal}
    (h : v =ᵐ[μ] w) : erealIntegral μ v = erealIntegral μ w := by
  unfold erealIntegral
  have h1 : (fun a => (v a ⊔ 0).toENNReal) =ᵐ[μ] fun a => (w a ⊔ 0).toENNReal :=
    h.mono fun a ha => by simp only [ha]
  have h2 : (fun a => ((-v a) ⊔ 0).toENNReal) =ᵐ[μ] fun a => ((-w a) ⊔ 0).toENNReal :=
    h.mono fun a ha => by simp only [ha]
  rw [lintegral_congr_ae h1, lintegral_congr_ae h2]

lemma lookAheadSet_meas (P : StationaryProblem E) : MeasurableSet (lookAheadSet P) :=
  measurableSet_le ((measurable_coe_real_ereal.comp P.c_meas).add
    ((measurable_erealIntegral P.QX P.QX_meas (measurable_coe_real_ereal.comp P.g_meas)).const_mul _))
    (measurable_coe_real_ereal.comp P.g_meas)

/-- On a closed `S_0`, any `v ≥ g` with `v = g` on `S_0` has `∫ v dQ(·|x) = ∫ g dQ(·|x)`
for `x ∈ S_0`. -/
lemma integral_eq_on (P : StationaryProblem E)
    (hclosed : ∀ x ∈ lookAheadSet P, P.QX x (lookAheadSet P) = 1) {v : E → EReal}
    (hv : ∀ y ∈ lookAheadSet P, v y = (P.g y : EReal)) {x : E} (hx : x ∈ lookAheadSet P) :
    erealIntegral (P.QX x) v = erealIntegral (P.QX x) (fun y => (P.g y : EReal)) := by
  have := P.QX_prob x
  apply erealIntegral_congr_ae
  have h0 : P.QX x (lookAheadSet P)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff (lookAheadSet_meas P)]; exact hclosed x hx
  have : ∀ᵐ y ∂(P.QX x), y ∈ lookAheadSet P := measure_eq_zero_iff_ae_notMem.1 h0 |>.mono
    fun y hy => by simpa using hy
  exact this.mono fun y hy => hv y hy

lemma lt_of_not_mem (P : StationaryProblem E) {v : E → EReal}
    (hv : ∀ y, (P.g y : EReal) ≤ v y) {x : E} (hx : x ∉ lookAheadSet P) :
    (P.g x : EReal) < (P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) v := by
  have h1 : (P.g x : EReal) < (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (P.g y : EReal)) := not_le.1 hx
  exact h1.trans_le (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (erealIntegral_mono _ hv) (beta_nonneg P)))

lemma maximizer_of (P : StationaryProblem E)
    (hclosed : ∀ x ∈ lookAheadSet P, P.QX x (lookAheadSet P) = 1) {v : E → EReal}
    (hg : ∀ y, (P.g y : EReal) ≤ v y) (hv : ∀ y ∈ lookAheadSet P, v y = (P.g y : EReal)) :
    P.IsMaximizer (lookAheadSet P) v := by
  refine ⟨lookAheadSet_meas P, fun x => ?_⟩
  unfold StationaryProblem.Tf StationaryProblem.T
  by_cases hx : x ∈ lookAheadSet P
  · rw [if_pos hx, integral_eq_on P hclosed hv hx]
    exact (max_eq_left hx).symm
  · rw [if_neg hx]
    exact (max_eq_right (lt_of_not_mem P hg hx).le).symm

lemma J_eq_g (P : StationaryProblem E)
    (hclosed : ∀ x ∈ lookAheadSet P, P.QX x (lookAheadSet P) = 1) (n : ℕ) :
    ∀ x ∈ lookAheadSet P, P.J n x = (P.g x : EReal) := by
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hx
    change max _ _ = _
    rw [integral_eq_on P hclosed ih hx]
    exact max_eq_left hx

lemma mem_stopSet_iff (P : StationaryProblem E)
    (hclosed : ∀ x ∈ lookAheadSet P, P.QX x (lookAheadSet P) = 1) (n : ℕ) (x : E) :
    x ∈ P.stopSet (n + 1) ↔ x ∈ lookAheadSet P := by
  constructor
  · intro h
    by_contra hx
    have h1 := lt_of_not_mem P (g_le_J P n) hx
    have h2 : (P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) (P.J n)
        ≤ P.J (n + 1) x := le_max_right _ _
    have h3 : P.J (n + 1) x = (P.g x : EReal) := h
    rw [h3] at h2
    exact absurd (h1.trans_le h2) (lt_irrefl _)
  · intro hx
    exact J_eq_g P hclosed (n + 1) x hx

lemma sInf_le_iff' (S : ℕ → Set E) (w : ℕ → E) (n : ℕ) :
    sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S k}) ≤ (n : ℕ∞) ↔ ∃ k ≤ n, w k ∈ S k := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : ((n + 1 : ℕ) : ℕ∞) ≤ sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S k}) := by
      refine le_sInf ?_
      rintro _ ⟨k, hk, rfl⟩
      have : ¬ k ≤ n := fun hkn => hc k hkn hk
      show ((n + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)
      exact_mod_cast (by omega : n + 1 ≤ k)
    have := this.trans h
    have : n + 1 ≤ n := by exact_mod_cast this
    omega
  · rintro ⟨k, hk, hS⟩
    have hmem : (k : ℕ∞) ∈ (fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S k} := ⟨k, hS, rfl⟩
    exact (sInf_le hmem).trans (by exact_mod_cast hk)

lemma enat_ext {a b : ℕ∞} (h : ∀ m : ℕ, a ≤ (m : ℕ∞) ↔ b ≤ (m : ℕ∞)) : a = b := by
  refine le_antisymm ?_ ?_
  · induction b using ENat.recTopCoe with
    | top => exact le_top
    | coe n => exact (h n).2 le_rfl
  · induction a using ENat.recTopCoe with
    | top => exact le_top
    | coe n => exact (h n).1 le_rfl

lemma capped_eq (P : StationaryProblem E)
    (hclosed : ∀ x ∈ lookAheadSet P, P.QX x (lookAheadSet P) = 1) (N : ℕ) :
    hitTimeCapped (fun n => P.stopSet (N - n)) N = truncTime (hitTime (lookAheadSet P)) N := by
  funext w
  unfold hitTimeCapped truncTime
  apply enat_ext
  intro m
  rw [min_le_iff, min_le_iff]
  change _ ∨ _ ↔ sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ (fun _ => lookAheadSet P) k})
    ≤ (m : ℕ∞) ∨ _
  rw [sInf_le_iff', sInf_le_iff', Nat.cast_le]
  by_cases hNm : N ≤ m
  · simp [hNm]
  · simp only [hNm, or_false]
    refine exists_congr fun k => and_congr_right fun hk => ?_
    obtain ⟨j, hj⟩ : ∃ j, N - k = j + 1 := ⟨N - k - 1, by omega⟩
    show w k ∈ P.stopSet (N - k) ↔ _
    rw [hj, mem_stopSet_iff P hclosed]

lemma BN_of_B (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hB : P.AssumptionB Pr)
    (N : ℕ) : P.AssumptionBN Pr N := by
  intro x
  obtain ⟨C, hC, h⟩ := hB.1 x
  refine ⟨C, hC, fun tau htau hle => h tau htau ?_⟩
  have : {w | tau w = ⊤} = ∅ := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h'
    have := hle w
    rw [h'] at this
    exact absurd this (by simp)
  rw [this, measure_empty]

end MDPS1027

open MDPS1027 in
open BauerleRiederMDP.Stopping in
theorem solution {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (hclosed : ∀ x ∈ lookAheadSet P, P.QX x (lookAheadSet P) = 1) :
    ((∀ n : ℕ, 1 ≤ n → P.IsMaximizer (lookAheadSet P) (P.J n)) ∧
      P.IsMaximizer (lookAheadSet P) P.Jlim) ∧
    ((∀ N : ℕ, IsOptimalUpTo P Pr N (truncTime (hitTime (lookAheadSet P)) N)) ∧
      (AssumptionBLim P Pr →
        (∀ x : E, Pr x {w | hitTime (lookAheadSet P) w = ⊤} = 0) →
        P.IsOptimal Pr (hitTime (lookAheadSet P)))) := by
  have hJlim_g : ∀ y, (P.g y : EReal) ≤ P.Jlim y := fun y => (g_le_J P 0 y).trans (J_le_Jlim P 0 y)
  have hJlim_eq : ∀ y ∈ lookAheadSet P, P.Jlim y = (P.g y : EReal) := fun y hy =>
    le_antisymm (iSup_le fun n => (J_eq_g P hclosed n y hy).le) (hJlim_g y)
  have hopt : ∀ N : ℕ, IsOptimalUpTo P Pr N (truncTime (hitTime (lookAheadSet P)) N) := by
    intro N
    have h := theorem_10_1_5 P N Pr hPr (BN_of_B P hB N)
    rw [← capped_eq P hclosed N]
    exact h.2.2.2.2.2.2.2
  have hval : ∀ (n : ℕ) (x : E), P.valueUpTo Pr n x = P.J n x := fun n x =>
    (theorem_10_1_5 P n Pr hPr (BN_of_B P hB n)).1.2.2 n le_rfl x
  refine ⟨⟨fun n _ => maximizer_of P hclosed (g_le_J P n) (J_eq_g P hclosed n),
    maximizer_of P hclosed hJlim_g hJlim_eq⟩, hopt, fun hBL hfin => ?_⟩
  have hstop := isStopTime_hitTime (lookAheadSet_meas P)
  refine ⟨hstop, hfin, fun x => ?_⟩
  have h1 := hBL.2 x _ hstop (hfin x)
  have h2 : Tendsto (fun n : ℕ => P.J n x) atTop (𝓝 (P.Jlim x)) := tendsto_atTop_iSup (J_mono P x)
  have h3 : (fun n : ℕ => P.EReward Pr (truncTime (hitTime (lookAheadSet P)) n) x) =
      fun n => P.J n x := funext fun n => ((hopt n).2.2 x).trans (hval n x)
  rw [h3] at h1
  rw [tendsto_nhds_unique h1 h2]
  exact ((theorem_10_2_2 P Pr hPr hB).1 x).1.symm
