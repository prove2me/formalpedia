-- Prove2me | solution 1 for BauerleRiederMDP.Stopping.theorem_10_1_5
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T20:37:20.287179+00:00
-- url     : https://prove2.me/submissions/aa5d16f0-42b8-4ad7-b7ae-51e55c10a0ea

import Definitions.Def_MDPFinance_OptimalStopping_Stationary
import Definitions.Def_BauerleRiederMDP_Stopping_IsOptimalUpTo
import Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_1_3

open MeasureTheory
open MDPFinance.OptimalStopping

namespace MDPS1015

variable {E : Type*} [MeasurableSpace E]

/-! ### Generic `EReal` / `erealIntegral` facts -/

lemma measurable_ereal_neg : Measurable (fun x : EReal => -x) := continuous_neg.measurable

lemma pos_toENNReal (e : EReal) : (e ⊔ 0).toENNReal = e.toENNReal := by
  rcases le_total e 0 with h | h
  · rw [sup_eq_right.2 h, EReal.toENNReal_of_nonpos h]; simp
  · rw [sup_eq_left.2 h]

lemma erealIntegral_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal) :
    erealIntegral μ v = ((∫⁻ x, (v x).toENNReal ∂μ : ENNReal) : EReal) +
      -((∫⁻ x, (-v x).toENNReal ∂μ : ENNReal) : EReal) := by
  simp only [erealIntegral, pos_toENNReal]

lemma ereal_split (e : EReal) :
    ((e.toENNReal : ENNReal) : EReal) + -(((-e).toENNReal : ENNReal) : EReal) = e := by
  induction e using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal,
      EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, ← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma erealIntegral_const_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal)
    {a : ℝ} (ha : 0 < a) :
    erealIntegral μ (fun w => (a : EReal) * v w) = (a : EReal) * erealIntegral μ v := by
  have hpos : ∀ e : EReal, ((a : EReal) * e).toENNReal = ENNReal.ofReal a * e.toENNReal := by
    intro e; rw [EReal.toENNReal_mul (by exact_mod_cast ha.le), EReal.real_coe_toENNReal]
  rw [erealIntegral_eq, erealIntegral_eq]
  simp only [← mul_neg, hpos]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    EReal.coe_ennreal_mul, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left ha.le,
    EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast ha.le) (EReal.coe_ne_top a), mul_neg]

lemma mul_iSup₂ {ι : Sort*} (p : ι → Prop) (f : ι → EReal) {a : ℝ} (ha : 0 < a) :
    (a : EReal) * (⨆ i, ⨆ (_ : p i), f i) = ⨆ i, ⨆ (_ : p i), (a : EReal) * f i := by
  have ha' : (0 : EReal) ≤ a := by exact_mod_cast ha.le
  have hb' : (0 : EReal) ≤ ((a⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 ha).le
  apply le_antisymm
  · have h1 : (⨆ i, ⨆ (_ : p i), f i) ≤
        ((a⁻¹ : ℝ) : EReal) * ⨆ i, ⨆ (_ : p i), (a : EReal) * f i := by
      refine iSup₂_le fun i hi => ?_
      calc f i = ((a⁻¹ : ℝ) : EReal) * ((a : EReal) * f i) := by
            rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ha.ne', EReal.coe_one, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_iSup₂_of_le i hi le_rfl) hb'
    calc (a : EReal) * _ ≤ (a : EReal) * (((a⁻¹ : ℝ) : EReal) *
          ⨆ i, ⨆ (_ : p i), (a : EReal) * f i) := mul_le_mul_of_nonneg_left h1 ha'
      _ = _ := by rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ha.ne', EReal.coe_one, one_mul]
  · exact iSup₂_le fun i hi => mul_le_mul_of_nonneg_left (le_iSup₂_of_le i hi le_rfl) ha'

lemma max_pow_le {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1) (k j : ℕ) (r : ℝ) :
    max (b ^ (k + j) * r) 0 ≤ b ^ j * max r 0 := by
  calc max (b ^ (k + j) * r) 0 = b ^ (k + j) * max r 0 := by
        rw [mul_max_of_nonneg _ _ (pow_nonneg h0 _), mul_zero]
    _ ≤ b ^ j * max r 0 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h0 h1 (Nat.le_add_left j k))
          (le_max_right _ _)

/-! ### The associated non-stationary problem -/

noncomputable def toQ (P : StationaryProblem E) (n : ℕ) : StoppingProblem E n where
  QX := fun _ => P.QX
  QX_prob := fun _ x => P.QX_prob x
  QX_meas := fun _ => P.QX_meas
  c := fun k x => P.beta ^ k * P.c x
  c_meas := fun _ => P.c_meas.const_mul _
  g := fun k x => P.beta ^ k * P.g x
  g_meas := fun _ => P.g_meas.const_mul _

lemma cyl_eq (P : StationaryProblem E) (n : ℕ) (m : ℕ) :
    ∀ (t : ℕ) (B : ℕ → Set E) (y : E), (toQ P n).cyl t m B y = P.cyl m B y := by
  induction m with
  | zero => intro t B y; rfl
  | succ m ih => intro t B y; simp only [StoppingProblem.cyl, StationaryProblem.cyl, ih]; rfl

lemma pathLaw (P : StationaryProblem E) (n : ℕ) {Pr : E → Measure (ℕ → E)}
    (hPr : P.IsPathLaw Pr) : (toQ P n).IsPathLaw (fun _ => Pr) := by
  refine ⟨fun _ x => hPr.1 x, fun k x m B hB => ?_⟩
  rw [hPr.2 x m B hB]
  simp only [cyl_eq]

lemma rewardFrom_eq (P : StationaryProblem E) (n k : ℕ) (tau : (ℕ → E) → ℕ∞) (w : ℕ → E) :
    (toQ P n).rewardFrom k tau w = P.beta ^ k * P.reward tau w := by
  unfold StoppingProblem.rewardFrom StationaryProblem.reward
  generalize tau w = t
  induction t using ENat.recTopCoe with
  | top => exact (mul_zero _).symm
  | coe m => simp [toQ, Finset.mul_sum, pow_add, mul_add, mul_assoc]

lemma EReward_zero (P : StationaryProblem E) (n : ℕ) (Pr : E → Measure (ℕ → E))
    (tau : (ℕ → E) → ℕ∞) (x : E) :
    (toQ P n).EReward (fun _ => Pr) 0 tau x = P.EReward Pr tau x := by
  unfold StoppingProblem.EReward StationaryProblem.EReward
  congr 1; funext w; rw [rewardFrom_eq]; simp

lemma Vn_eq (P : StationaryProblem E) (n k : ℕ) (Pr : E → Measure (ℕ → E)) (x : E) :
    (toQ P n).Vn (fun _ => Pr) k x = ((P.beta ^ k : ℝ) : EReal) * P.valueUpTo Pr (n - k) x := by
  unfold StoppingProblem.Vn StationaryProblem.valueUpTo
  refine Eq.trans ?_ (mul_iSup₂ _ _ (pow_pos P.beta_mem.1 k)).symm
  refine iSup_congr fun tau => iSup_congr fun _ => ?_
  unfold StoppingProblem.EReward StationaryProblem.EReward
  simp only [rewardFrom_eq, EReal.coe_mul]
  exact erealIntegral_const_mul _ _ (pow_pos P.beta_mem.1 k)

lemma BN (P : StationaryProblem E) {N n : ℕ} (hn : n ≤ N) {Pr : E → Measure (ℕ → E)}
    (hBN : P.AssumptionBN Pr N) : (toQ P n).AssumptionBN (fun _ => Pr) := by
  intro k _ x
  obtain ⟨C, hC, hb⟩ := hBN x
  refine ⟨C, hC, fun tau htau hle => le_trans ?_ (hb tau htau fun w => (hle w).trans
    (by exact_mod_cast (Nat.sub_le n k).trans hn))⟩
  refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
  have h0 := P.beta_mem.1.le
  have h1 := P.beta_mem.2
  simp only [toQ]
  exact add_le_add (Finset.sum_le_sum fun j _ => max_pow_le h0 h1 k j _) (max_pow_le h0 h1 k _ _)

lemma T_zero (P : StationaryProblem E) (n : ℕ) (v : E → EReal) (x : E) :
    (toQ P n).T 0 (fun y => ((P.beta ^ 1 : ℝ) : EReal) * v y) x = P.T v x := by
  unfold StoppingProblem.T StationaryProblem.T
  rw [erealIntegral_const_mul _ _ (pow_pos P.beta_mem.1 1)]
  simp [toQ]

/-! ### Part a) -/

lemma valueUpTo_zero (P : StationaryProblem E) {N : ℕ} {Pr : E → Measure (ℕ → E)}
    (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) (x : E) :
    P.valueUpTo Pr 0 x = (P.g x : EReal) := by
  have h := ((MDPFinance.OptimalStopping.theorem_10_1_3 (toQ P 0) (fun _ => Pr) (pathLaw P 0 hPr)
    (BN P (Nat.zero_le N) hBN)).1.1 x)
  rw [Vn_eq] at h
  simpa [toQ] using h

lemma valueUpTo_succ (P : StationaryProblem E) {N : ℕ} {Pr : E → Measure (ℕ → E)}
    (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) (n : ℕ) (h1 : 1 ≤ n) (hn : n ≤ N)
    (x : E) : P.valueUpTo Pr n x = P.T (P.valueUpTo Pr (n - 1)) x := by
  have h := ((MDPFinance.OptimalStopping.theorem_10_1_3 (toQ P n) (fun _ => Pr) (pathLaw P n hPr)
    (BN P hn hBN)).1.2 0 (by omega) x)
  have hV : (toQ P n).Vn (fun _ => Pr) (0 + 1) =
      fun y => ((P.beta ^ 1 : ℝ) : EReal) * P.valueUpTo Pr (n - 1) y := by
    funext y; rw [Vn_eq]
  rw [hV, T_zero, Vn_eq] at h
  simpa using h

lemma valueUpTo_eq_J (P : StationaryProblem E) {N : ℕ} {Pr : E → Measure (ℕ → E)}
    (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) :
    ∀ n : ℕ, n ≤ N → ∀ x : E, P.valueUpTo Pr n x = P.J n x := by
  intro n
  induction n with
  | zero => intro _ x; rw [valueUpTo_zero P hPr hBN]; rfl
  | succ m ih =>
    intro hm x
    rw [valueUpTo_succ P hPr hBN (m + 1) (by omega) hm x]
    simp only [Nat.add_sub_cancel]
    have : P.valueUpTo Pr m = P.J m := funext (ih (by omega))
    rw [this]; rfl

/-! ### Part b) -/

lemma g_le_valueUpTo (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)}
    (hPr : P.IsPathLaw Pr) (n : ℕ) (x : E) : (P.g x : EReal) ≤ P.valueUpTo Pr n x := by
  have hmap : (Pr x).map (fun w : ℕ → E => w 0) = Measure.dirac x := by
    ext B hB
    rw [Measure.map_apply (measurable_pi_apply 0) hB, Measure.dirac_apply' x hB]
    have h := hPr.2 x 0 (fun _ => B) (fun _ => hB)
    have hs : {w : ℕ → E | ∀ i ≤ 0, w i ∈ B} = (fun w : ℕ → E => w 0) ⁻¹' B := by
      ext w; simp
    rw [hs] at h
    rw [h]; rfl
  have hF : ∀ F : E → ENNReal, Measurable F → ∫⁻ w, F (w 0) ∂(Pr x) = F x := by
    intro F hF
    rw [← lintegral_map hF (measurable_pi_apply 0), hmap, lintegral_dirac' x hF]
  have hgm : Measurable fun y => (P.g y : EReal) := measurable_coe_real_ereal.comp P.g_meas
  have hR : P.EReward Pr (fun _ => ((0 : ℕ) : ℕ∞)) x = P.g x := by
    have hrw : (fun w => (P.reward (fun _ => ((0 : ℕ) : ℕ∞)) w : EReal)) =
        fun w => (P.g (w 0) : EReal) := by
      funext w; simp [StationaryProblem.reward]
    unfold StationaryProblem.EReward
    rw [hrw, erealIntegral_eq, hF _ hgm.ereal_toENNReal,
      hF (fun y => (-(P.g y : EReal)).toENNReal) (measurable_ereal_neg.comp hgm).ereal_toENNReal]
    exact ereal_split _
  refine le_iSup₂_of_le (fun _ => ((0 : ℕ) : ℕ∞)) ⟨fun k => MeasurableSet.const _,
    fun w => by simp⟩ (le_of_eq hR.symm)

lemma valueUpTo_mono (P : StationaryProblem E) (Pr : E → Measure (ℕ → E)) (n : ℕ) (x : E) :
    P.valueUpTo Pr n x ≤ P.valueUpTo Pr (n + 1) x := by
  unfold StationaryProblem.valueUpTo
  refine iSup_le fun tau => iSup_le fun h => le_iSup₂_of_le tau ⟨h.1, fun w => (h.2 w).trans ?_⟩ le_rfl
  exact_mod_cast Nat.le_succ n

/-! ### Parts c), d) -/

lemma ereal_neg_nonpos {a : EReal} : -a ≤ 0 ↔ 0 ≤ a := by rw [EReal.neg_le, neg_zero]

lemma measurable_I (P : StationaryProblem E) {v : E → EReal} (hv : Measurable v) :
    Measurable fun x => erealIntegral (P.QX x) v := by
  have hp : Measurable fun y => (v y ⊔ 0).toENNReal := (hv.max measurable_const).ereal_toENNReal
  have hn : Measurable fun y => ((-v y) ⊔ 0).toENNReal :=
    ((measurable_ereal_neg.comp hv).max measurable_const).ereal_toENNReal
  unfold erealIntegral
  exact (measurable_coe_ennreal_ereal.comp ((Measure.measurable_lintegral hp).comp P.QX_meas)).add
    (measurable_ereal_neg.comp
      (measurable_coe_ennreal_ereal.comp ((Measure.measurable_lintegral hn).comp P.QX_meas)))

lemma max_eq_aux (g c : ℝ) (z : EReal) :
    max (g : EReal) (c + z) = g + max (-((g : EReal) - c - z)) 0 := by
  rw [← EReal.coe_sub]
  induction z using EReal.rec with
  | bot => rw [EReal.coe_sub_bot, EReal.neg_top, max_eq_right bot_le, add_zero, EReal.add_bot,
      max_eq_left bot_le]
  | top => simp
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_neg]
    rcases le_total g (c + r) with h | h
    · rw [max_eq_right (EReal.coe_le_coe_iff.2 h),
        max_eq_left (show (0 : EReal) ≤ ((-(g - c - r) : ℝ) : EReal) by
          exact_mod_cast (show (0 : ℝ) ≤ -(g - c - r) by linarith)), ← EReal.coe_add]
      congr 1; ring
    · rw [max_eq_left (EReal.coe_le_coe_iff.2 h),
        max_eq_right (show ((-(g - c - r) : ℝ) : EReal) ≤ 0 by
          exact_mod_cast (show -(g - c - r) ≤ (0 : ℝ) by linarith)), add_zero]

lemma J_meas (P : StationaryProblem E) (n : ℕ) : Measurable (P.J n) := by
  induction n with
  | zero => exact measurable_coe_real_ereal.comp P.g_meas
  | succ m ih =>
    show Measurable (P.T (P.J m))
    unfold StationaryProblem.T
    exact (measurable_coe_real_ereal.comp P.g_meas).max
      ((measurable_coe_real_ereal.comp P.c_meas).add (measurable_const.mul (measurable_I P ih)))

lemma measurable_d (P : StationaryProblem E) (n : ℕ) : Measurable (P.d n) := by
  have : P.d n = fun x => (P.g x : EReal) + -(P.c x : EReal) +
      -((P.beta : EReal) * erealIntegral (P.QX x) (P.J (n - 1))) := by
    funext x; simp only [StationaryProblem.d, sub_eq_add_neg]
  rw [this]
  exact ((measurable_coe_real_ereal.comp P.g_meas).add
    (measurable_ereal_neg.comp (measurable_coe_real_ereal.comp P.c_meas))).add
    (measurable_ereal_neg.comp (measurable_const.mul (measurable_I P (J_meas P _))))

lemma J_eq (P : StationaryProblem E) (n : ℕ) (h1 : 1 ≤ n) (y : E) :
    P.J n y = (P.g y : EReal) + max (-P.d n y) 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show P.T (P.J m) y = _
  unfold StationaryProblem.T StationaryProblem.d
  simp only [Nat.add_sub_cancel]
  exact max_eq_aux _ _ _

lemma stopSet_eq (P : StationaryProblem E) (n : ℕ) (h1 : 1 ≤ n) :
    P.stopSet n = {x : E | 0 ≤ P.d n x} := by
  ext x
  simp only [StationaryProblem.stopSet, Set.mem_ofPred_eq, J_eq P n h1]
  have key : ∀ (g : ℝ) (m : EReal), 0 ≤ m → ((g : EReal) + m = g ↔ m = 0) := by
    intro g m hm
    induction m using EReal.rec with
    | bot => exact absurd hm (by simp)
    | top => simp
    | coe r =>
      constructor
      · intro h
        rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
        exact_mod_cast (by linarith : r = 0)
      · intro h; rw [h, add_zero]
  rw [key _ _ (le_max_right _ _)]
  constructor
  · intro h; have : -P.d n x ≤ 0 := h ▸ le_max_left _ _
    exact ereal_neg_nonpos.1 this
  · intro h; exact max_eq_right (ereal_neg_nonpos.2 h)

lemma Ag_fin (P : StationaryProblem E) {N : ℕ} {Pr : E → Measure (ℕ → E)}
    (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) (hN : 1 ≤ N) (x : E) :
    ∫⁻ y, ((P.g y : EReal)).toENNReal ∂(P.QX x) < ⊤ := by
  obtain ⟨C, hC, hb⟩ := hBN x
  have hst : IsStopTime (fun _ : ℕ → E => ((1 : ℕ) : ℕ∞)) := fun k => MeasurableSet.const _
  have h := hb _ hst (fun w => by exact_mod_cast hN)
  have hmap : (Pr x).map (fun w : ℕ → E => w 1) = P.QX x := by
    ext B hB
    rw [Measure.map_apply (measurable_pi_apply 1) hB]
    let B' : ℕ → Set E := fun i => if i = 1 then B else Set.univ
    have hB' : ∀ i, MeasurableSet (B' i) := by
      intro i; by_cases hi : i = 1 <;> simp [B', hi, hB]
    have h := hPr.2 x 1 B' hB'
    have hs : {w : ℕ → E | ∀ i ≤ 1, w i ∈ B' i} = (fun w : ℕ → E => w 1) ⁻¹' B := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · intro hw; simpa [B'] using hw 1 le_rfl
      · intro hw i _; by_cases hi : i = 1
        · subst hi; simpa [B'] using hw
        · simp [B', hi]
    rw [hs] at h
    rw [h]
    simp [B', StationaryProblem.cyl]
  have hgm : Measurable fun y => (P.g y : EReal).toENNReal :=
    (measurable_coe_real_ereal.comp P.g_meas).ereal_toENNReal
  have hle : ENNReal.ofReal P.beta * ∫⁻ y, (P.g y : EReal).toENNReal ∂(P.QX x) ≤ C := by
    rw [← hmap, lintegral_map hgm (measurable_pi_apply 1),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (lintegral_mono fun w => ?_) h
    simp only [ENat.toNat_natCast, Finset.sum_range_one, pow_zero, one_mul, pow_one,
      EReal.real_coe_toENNReal]
    rw [← ENNReal.ofReal_mul P.beta_mem.1.le]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [le_max_left (P.g (w 1)) 0, le_max_right (P.c (w 0)) 0, P.beta_mem.1]
  have hβ : ENNReal.ofReal P.beta ≠ 0 := by simp [P.beta_mem.1]
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.mul_top hβ] at hle
  exact absurd (lt_of_le_of_lt hle hC) (lt_irrefl _)

lemma pw_identity (u : ℝ) (h : EReal) (hh : 0 ≤ h) :
    (((u : EReal) + h).toENNReal + (-(u : EReal)).toENNReal) =
      (-((u : EReal) + h)).toENNReal + (u : EReal).toENNReal + h.toENNReal := by
  induction h using EReal.rec with
  | bot => exact absurd hh (by simp)
  | top => simp
  | coe r =>
    have hr : (0 : ℝ) ≤ r := by exact_mod_cast hh
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_ofReal']
    rcases le_total u 0 with h1 | h1 <;> rcases le_total (u + r) 0 with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2, neg_nonneg, neg_nonpos, hr] <;> linarith

lemma ennreal_arith {A' B' Ag Bg H : ENNReal} (key : A' + Bg = B' + Ag + H) (hB' : B' ≤ Bg)
    (hAg : Ag < ⊤) (hnd : ¬ ((Ag : EReal) + -(Bg : EReal) = ⊥ ∧ (H : EReal) = ⊤)) :
    (A' : EReal) + -(B' : EReal) = ((Ag : EReal) + -(Bg : EReal)) + (H : EReal) := by
  lift Ag to NNReal using hAg.ne with ag
  by_cases hH : H = ⊤
  · subst hH
    have hBg : Bg ≠ ⊤ := by
      rintro rfl; exact hnd ⟨by simp, by simp⟩
    lift Bg to NNReal using hBg with bg
    have hA' : A' = ⊤ := by
      by_contra hA; lift A' to NNReal using hA with a; simp at key
    have hB'f : B' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hB'
    lift B' to NNReal using hB'f with b
    subst hA'
    simp only [EReal.coe_ennreal_top]
    rw [show ((b : ENNReal) : EReal) = ((b : ℝ) : EReal) from rfl,
      show ((ag : ENNReal) : EReal) = ((ag : ℝ) : EReal) from rfl,
      show ((bg : ENNReal) : EReal) = ((bg : ℝ) : EReal) from rfl, ← EReal.coe_neg, ← EReal.coe_neg,
      ← EReal.coe_add, EReal.top_add_coe, EReal.coe_add_top]
  · lift H to NNReal using hH with hv
    by_cases hBg : Bg = ⊤
    · subst hBg
      have hB'top : B' = ⊤ := by
        by_contra hB; lift B' to NNReal using hB with b
        rw [add_top] at key
        exact absurd key.symm (by rw [← ENNReal.coe_add, ← ENNReal.coe_add]; exact ENNReal.coe_ne_top)
      subst hB'top
      simp
    · lift Bg to NNReal using hBg with bg
      have hB'f : B' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hB'
      lift B' to NNReal using hB'f with b
      have hA'f : A' ≠ ⊤ := by
        rintro rfl; rw [top_add] at key; exact absurd key.symm (by rw [← ENNReal.coe_add, ← ENNReal.coe_add]; exact ENNReal.coe_ne_top)
      lift A' to NNReal using hA'f with a
      have key' : (a : ℝ) + bg = b + ag + hv := by
        norm_cast at key
        have := congrArg NNReal.toReal key
        push_cast at this
        linarith
      rw [show ((b : ENNReal) : EReal) = ((b : ℝ) : EReal) from rfl,
        show ((a : ENNReal) : EReal) = ((a : ℝ) : EReal) from rfl,
        show ((ag : ENNReal) : EReal) = ((ag : ℝ) : EReal) from rfl,
        show ((hv : ENNReal) : EReal) = ((hv : ℝ) : EReal) from rfl,
        show ((bg : ENNReal) : EReal) = ((bg : ℝ) : EReal) from rfl, ← EReal.coe_neg, ← EReal.coe_neg,
        ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
      congr 1; linarith

lemma int_add {α : Type*} [MeasurableSpace α] (μ : Measure α) (u : α → ℝ) (hu : Measurable u)
    (h : α → EReal) (hhm : Measurable h) (hh0 : ∀ y, 0 ≤ h y)
    (hAg : ∫⁻ y, (u y : EReal).toENNReal ∂μ < ⊤)
    (hnd : ¬ (erealIntegral μ (fun y => (u y : EReal)) = ⊥ ∧ erealIntegral μ h = ⊤)) :
    erealIntegral μ (fun y => (u y : EReal) + h y) =
      erealIntegral μ (fun y => (u y : EReal)) + erealIntegral μ h := by
  have hum : Measurable fun y => (u y : EReal) := measurable_coe_real_ereal.comp hu
  have hz : ∫⁻ y, (-h y).toENNReal ∂μ = 0 := by
    rw [lintegral_congr fun y => EReal.toENNReal_of_nonpos (ereal_neg_nonpos.2 (hh0 y)),
      lintegral_zero]
  have hIh : erealIntegral μ h = ((∫⁻ y, (h y).toENNReal ∂μ : ENNReal) : EReal) := by
    rw [erealIntegral_eq, hz]; simp
  rw [hIh] at hnd ⊢
  rw [erealIntegral_eq] at hnd
  rw [erealIntegral_eq, erealIntegral_eq]
  refine ennreal_arith ?_ ?_ hAg hnd
  · have h1 := lintegral_congr (μ := μ) fun y => pw_identity (u y) (h y) (hh0 y)
    rw [lintegral_add_right _ (show Measurable fun y => (-(u y : EReal)).toENNReal from
        (measurable_ereal_neg.comp hum).ereal_toENNReal),
      lintegral_add_right _ (show Measurable fun y => (h y).toENNReal from hhm.ereal_toENNReal),
      lintegral_add_right _ (show Measurable fun y => ((u y : EReal)).toENNReal from
        hum.ereal_toENNReal)] at h1
    exact h1
  · refine lintegral_mono fun y => EReal.toENNReal_le_toENNReal ?_
    exact EReal.neg_le_neg_iff.2 (le_add_of_nonneg_right (hh0 y))

lemma ereal_arith (g c b : ℝ) (hb : 0 < b) (X Y : EReal) (hX : X ≠ ⊤) (hY : 0 ≤ Y)
    (hnd : ¬ (X = ⊥ ∧ Y = ⊤)) :
    (g : EReal) - c - b * (X + Y) = ((g : EReal) - c - b * X) - b * Y := by
  rw [← EReal.coe_sub]
  induction X using EReal.rec with
  | top => exact absurd rfl hX
  | bot =>
    induction Y using EReal.rec with
    | bot => exact absurd hY (by simp)
    | top => exact absurd ⟨rfl, rfl⟩ hnd
    | coe r =>
      rw [EReal.bot_add, EReal.coe_mul_bot_of_pos hb, EReal.coe_sub_bot, ← EReal.coe_mul,
        EReal.top_sub_coe]
  | coe s =>
    induction Y using EReal.rec with
    | bot => exact absurd hY (by simp)
    | top =>
      rw [EReal.coe_add_top, EReal.coe_mul_top_of_pos hb, EReal.sub_top, ← EReal.coe_mul,
        ← EReal.coe_sub, EReal.sub_top]
    | coe r =>
      rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub,
        ← EReal.coe_sub, ← EReal.coe_sub]
      congr 1; ring

lemma part_c (P : StationaryProblem E) {N : ℕ} {Pr : E → Measure (ℕ → E)}
    (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) (n : ℕ) (x : E) (h1 : 1 ≤ n)
    (hN : n + 1 ≤ N)
    (hnd : ¬ (P.d 1 x = ⊤ ∧ erealIntegral (P.QX x) (fun y => max (-P.d n y) 0) = ⊤)) :
    P.d (n + 1) x =
      P.d 1 x - (P.beta : EReal) * erealIntegral (P.QX x) (fun y => max (-P.d n y) 0) := by
  have hJn : P.J n = fun y => (P.g y : EReal) + max (-P.d n y) 0 := funext (J_eq P n h1)
  have hd1 : P.d 1 x = (P.g x : EReal) - P.c x -
      (P.beta : EReal) * erealIntegral (P.QX x) (fun y => (P.g y : EReal)) := rfl
  have hdn1 : P.d (n + 1) x = (P.g x : EReal) - P.c x -
      (P.beta : EReal) * erealIntegral (P.QX x) (P.J n) := by
    simp only [StationaryProblem.d, Nat.add_sub_cancel]
  have hAg := Ag_fin P hPr hBN (by omega) x
  have hhm : Measurable (fun y => max (-P.d n y) 0) :=
    (measurable_ereal_neg.comp (measurable_d P n)).max measurable_const
  have hnd' : ¬ (erealIntegral (P.QX x) (fun y => (P.g y : EReal)) = ⊥ ∧
      erealIntegral (P.QX x) (fun y => max (-P.d n y) 0) = ⊤) := by
    rintro ⟨e1, e2⟩
    apply hnd
    refine ⟨?_, e2⟩
    rw [hd1, e1, EReal.coe_mul_bot_of_pos P.beta_mem.1, ← EReal.coe_sub, EReal.coe_sub_bot]
  have hadd := int_add (P.QX x) P.g P.g_meas _ hhm (fun y => le_max_right _ _) hAg hnd'
  have hne : erealIntegral (P.QX x) (fun y => (P.g y : EReal)) ≠ ⊤ := by
    rw [erealIntegral_eq]
    lift (∫⁻ y, (P.g y : EReal).toENNReal ∂P.QX x) to NNReal using hAg.ne with a
    intro hc
    have hle : ((a : ℝ) : EReal) + -((∫⁻ y, (-(P.g y : EReal)).toENNReal ∂P.QX x : ENNReal) : EReal)
        ≤ ((a : ℝ) : EReal) :=
      add_le_of_nonpos_right (ereal_neg_nonpos.2 (EReal.coe_ennreal_nonneg _))
    rw [show ((a : ENNReal) : EReal) = ((a : ℝ) : EReal) from rfl] at hc
    rw [hc] at hle
    exact EReal.coe_ne_top _ (top_le_iff.1 hle)
  have hY : 0 ≤ erealIntegral (P.QX x) (fun y => max (-P.d n y) 0) := by
    rw [erealIntegral_eq]
    have hz : ∫⁻ y, (-(max (-P.d n y) 0)).toENNReal ∂P.QX x = 0 := by
      rw [lintegral_congr fun y =>
        EReal.toENNReal_of_nonpos (ereal_neg_nonpos.2 (le_max_right (-P.d n y) 0)), lintegral_zero]
    rw [hz]; simp only [EReal.coe_ennreal_zero, neg_zero, add_zero]; exact EReal.coe_ennreal_nonneg _
  rw [hdn1, hJn, hadd, hd1]
  exact ereal_arith _ _ _ P.beta_mem.1 _ _ hne hY hnd'

lemma mul_cancel_pos {b : ℝ} (hb : 0 < b) {u v : EReal} (h : (b : EReal) * u = b * v) :
    u = v := by
  have h' := congrArg (fun t => ((b⁻¹ : ℝ) : EReal) * t) h
  simp only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hb.ne', EReal.coe_one, one_mul] at h'
  exact h'

lemma optimal (P : StationaryProblem E) {N : ℕ} {Pr : E → Measure (ℕ → E)}
    (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) :
    BauerleRiederMDP.Stopping.IsOptimalUpTo P Pr N
      (hitTimeCapped (fun n => P.stopSet (N - n)) N) := by
  have h := (MDPFinance.OptimalStopping.theorem_10_1_3 (toQ P N) (fun _ => Pr) (pathLaw P N hPr)
    (BN P le_rfl hBN)).2
  have hS : (fun n => {x | (toQ P N).Vn (fun _ => Pr) n x = ((toQ P N).g n x : EReal)}) =
      fun n => P.stopSet (N - n) := by
    funext k; ext x
    simp only [Set.mem_ofPred_eq, StationaryProblem.stopSet]
    rw [Vn_eq, ← valueUpTo_eq_J P hPr hBN (N - k) (Nat.sub_le N k)]
    show _ = (((P.beta ^ k * P.g x : ℝ)) : EReal) ↔ _
    rw [EReal.coe_mul]
    constructor
    · intro he; exact mul_cancel_pos (pow_pos P.beta_mem.1 k) he
    · intro he; rw [he]
  rw [hS] at h
  refine ⟨h.1, h.2.1, fun x => ?_⟩
  rw [← EReward_zero P N, h.2.2 x, Vn_eq]
  simp

end MDPS1015

open MDPFinance.OptimalStopping in
theorem solution {E : Type*} [MeasurableSpace E] (P : StationaryProblem E) (N : ℕ)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr N) :
    ((∀ x : E, P.valueUpTo Pr 0 x = (P.g x : EReal)) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ x : E,
        P.valueUpTo Pr n x = P.T (P.valueUpTo Pr (n - 1)) x) ∧
      (∀ n : ℕ, n ≤ N → ∀ x : E, P.valueUpTo Pr n x = P.J n x)) ∧
    (∀ (n : ℕ) (x : E), (P.g x : EReal) ≤ P.valueUpTo Pr n x ∧
      P.valueUpTo Pr n x ≤ P.valueUpTo Pr (n + 1) x) ∧
    (∀ (n : ℕ) (x : E), 1 ≤ n → n + 1 ≤ N →
      ¬ (P.d 1 x = ⊤ ∧ erealIntegral (P.QX x) (fun y => max (-P.d n y) 0) = ⊤) →
      P.d (n + 1) x =
        P.d 1 x - (P.beta : EReal) * erealIntegral (P.QX x) (fun y => max (-P.d n y) 0)) ∧
    (P.stopSet 0 = Set.univ ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N → P.stopSet n = {x : E | 0 ≤ P.d n x}) ∧
      (∀ n : ℕ, n < N → P.stopSet (n + 1) ⊆ P.stopSet n) ∧
      BauerleRiederMDP.Stopping.IsOptimalUpTo P Pr N
        (policyTime (fun k => P.stopSet (N - k)) N) ∧
      BauerleRiederMDP.Stopping.IsOptimalUpTo P Pr N
        (hitTimeCapped (fun n => P.stopSet (N - n)) N)) := by
  refine ⟨⟨MDPS1015.valueUpTo_zero P hPr hBN, MDPS1015.valueUpTo_succ P hPr hBN,
    MDPS1015.valueUpTo_eq_J P hPr hBN⟩,
    fun n x => ⟨MDPS1015.g_le_valueUpTo P hPr n x, MDPS1015.valueUpTo_mono P Pr n x⟩,
    fun n x h1 hN hnd => MDPS1015.part_c P hPr hBN n x h1 hN hnd,
    ⟨?_, fun n h1 _ => MDPS1015.stopSet_eq P n h1, ?_, MDPS1015.optimal P hPr hBN,
      MDPS1015.optimal P hPr hBN⟩⟩
  · ext x; simp [StationaryProblem.stopSet, StationaryProblem.J]
  · intro n hn x hx
    have e1 := MDPS1015.valueUpTo_eq_J P hPr hBN n hn.le x
    have e2 := MDPS1015.valueUpTo_eq_J P hPr hBN (n + 1) hn x
    have m := MDPS1015.valueUpTo_mono P Pr n x
    have g1 := MDPS1015.g_le_valueUpTo P hPr n x
    simp only [StationaryProblem.stopSet, Set.mem_ofPred_eq] at hx ⊢
    rw [← e1]; rw [← e2] at hx
    exact le_antisymm (hx ▸ m) g1
