-- Prove2me | solution 1 for GT.SLA.energy_refined
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:41:43.873703+00:00
-- url     : https://prove2.me/submissions/c9e00825-c36e-4ea6-b709-422705d44860

import Mathlib
import Definitions.Def_GreenTaoFourCore

section File_KM_Bohr
/-!
# Bohr sets in `ZMod N`

We define the circle distance `cn`, Bohr sets `bohr Γ ρ`, prove the basic covering bound
`|bohr Γ ρ| ≤ (4ρ/ρ')^d |bohr Γ ρ'|`, the absolute lower bound `|bohr Γ ρ| ≥ N (ρ/2)^d`, and the
existence of regular radii.
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma cn_nonneg (z : ZMod N) : 0 ≤ cn z := norm_nonneg _

@[simp] lemma cn_neg (z : ZMod N) : cn (-z) = cn z := by simp [cn]

@[simp] lemma cn_zero : cn (0 : ZMod N) = 0 := by simp [cn]

lemma cn_add_le (a b : ZMod N) : cn (a + b) ≤ cn a + cn b := by
  simp only [cn, map_add]; exact norm_add_le _ _

lemma cn_natCast_mul_le (n : ℕ) (z : ZMod N) : cn ((n : ZMod N) * z) ≤ n * cn z := by
  simp only [cn]
  rw [← nsmul_eq_mul, map_nsmul]
  exact norm_nsmul_le

/-- A signed representative of `z / N` in `[-1/2, 1/2]`. -/
def sc (z : ZMod N) : ℝ := (z.val : ℝ) / N - round ((z.val : ℝ) / N)

lemma toAddCircle_eq_sc (z : ZMod N) : ZMod.toAddCircle z = ((sc z : ℝ) : UnitAddCircle) := by
  rw [ZMod.toAddCircle_apply, sc, AddCircle.coe_sub]
  have : (((round ((z.val : ℝ) / N) : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨round ((z.val : ℝ) / N), by simp⟩
  rw [this, sub_zero]

lemma cn_eq_abs_sc (z : ZMod N) : cn z = |sc z| := by
  rw [cn, toAddCircle_eq_sc, AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero]
  simpa [sc] using abs_sub_round ((z.val : ℝ) / N)

lemma norm_coe_le_abs (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  rw [AddCircle.norm_eq]
  simpa using round_le x 0

lemma cn_sub_le_abs (x y : ZMod N) : cn (x - y) ≤ |sc x - sc y| := by
  rw [cn, map_sub, toAddCircle_eq_sc, toAddCircle_eq_sc, ← AddCircle.coe_sub]
  exact norm_coe_le_abs _

variable {Γ Γ' : Finset (ZMod N)} {ρ ρ' : ℝ} {x y : ZMod N}

@[simp] lemma mem_bohr : x ∈ bohr Γ ρ ↔ ∀ γ ∈ Γ, cn (γ * x) ≤ ρ := by simp [bohr]

lemma zero_mem_bohr (hρ : 0 ≤ ρ) : (0 : ZMod N) ∈ bohr Γ ρ := by simp [hρ]

lemma neg_mem_bohr (hx : x ∈ bohr Γ ρ) : -x ∈ bohr Γ ρ := by
  rw [mem_bohr] at *
  intro γ hγ
  rw [mul_neg, cn_neg]; exact hx γ hγ

lemma add_mem_bohr (hx : x ∈ bohr Γ ρ) (hy : y ∈ bohr Γ ρ') : x + y ∈ bohr Γ (ρ + ρ') := by
  rw [mem_bohr] at *
  intro γ hγ
  rw [mul_add]; exact (cn_add_le _ _).trans (add_le_add (hx γ hγ) (hy γ hγ))

lemma sub_mem_bohr (hx : x ∈ bohr Γ ρ) (hy : y ∈ bohr Γ ρ') : x - y ∈ bohr Γ (ρ + ρ') := by
  rw [sub_eq_add_neg]; exact add_mem_bohr hx (neg_mem_bohr hy)

lemma bohr_mono (h : ρ ≤ ρ') : bohr Γ ρ ⊆ bohr Γ ρ' := by
  intro x hx
  rw [mem_bohr] at *
  exact fun γ hγ => (hx γ hγ).trans h

lemma bohr_anti (h : Γ ⊆ Γ') : bohr Γ' ρ ⊆ bohr Γ ρ := by
  intro x hx
  rw [mem_bohr] at *
  exact fun γ hγ => hx γ (h hγ)

lemma bohr_nonempty (hρ : 0 ≤ ρ) : (bohr Γ ρ).Nonempty := ⟨0, zero_mem_bohr hρ⟩

lemma bohr_card_pos (hρ : 0 ≤ ρ) : 0 < (bohr Γ ρ).card := (bohr_nonempty hρ).card_pos

/-! ### The covering bound -/

lemma card_Icc_floor_le {r : ℝ} (hr : 1 ≤ r) :
    ((Finset.Icc ⌊-r⌋ ⌊r⌋).card : ℝ) ≤ 4 * r := by
  rw [Int.card_Icc]
  have h1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le r
  have h2 : -r - 1 < (⌊-r⌋ : ℝ) := by have := Int.sub_one_lt_floor (-r); linarith
  have h3 : (0 : ℤ) ≤ ⌊r⌋ + 1 - ⌊-r⌋ := by
    have : ⌊-r⌋ ≤ ⌊r⌋ := Int.floor_mono (by linarith)
    omega
  have : ((⌊r⌋ + 1 - ⌊-r⌋).toNat : ℝ) = ((⌊r⌋ + 1 - ⌊-r⌋ : ℤ) : ℝ) := by
    rw [show (((⌊r⌋ + 1 - ⌊-r⌋).toNat : ℕ) : ℝ) = (((⌊r⌋ + 1 - ⌊-r⌋).toNat : ℤ) : ℝ) by norm_cast,
      Int.toNat_of_nonneg h3]
  rw [this]; push_cast; linarith

theorem card_bohr_le (Γ : Finset (ZMod N)) (h' : 0 < ρ') (h : ρ' ≤ ρ) :
    ((bohr Γ ρ).card : ℝ) ≤ (4 * ρ / ρ') ^ Γ.card * (bohr Γ ρ').card := by
  classical
  set r := ρ / ρ' with hr_def
  have hr : 1 ≤ r := by rw [hr_def, le_div_iff₀ h']; linarith
  let box : ZMod N → (Γ → ℤ) := fun x γ => ⌊sc (γ.1 * x) / ρ'⌋
  let T : Finset (Γ → ℤ) := Fintype.piFinset fun _ => Finset.Icc ⌊-r⌋ ⌊r⌋
  have himg : (bohr Γ ρ).image box ⊆ T := by
    intro v hv
    rw [mem_image] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    rw [Fintype.mem_piFinset]
    intro γ
    rw [mem_bohr] at hx
    have hγ := hx γ.1 γ.2
    rw [cn_eq_abs_sc, abs_le] at hγ
    rw [Finset.mem_Icc]
    constructor
    · apply Int.floor_mono
      rw [hr_def, ← neg_div, div_le_div_iff_of_pos_right h']; linarith
    · apply Int.floor_mono
      rw [hr_def, div_le_div_iff_of_pos_right h']; linarith
  have hfib : ∀ v ∈ (bohr Γ ρ).image box,
      ((bohr Γ ρ).filter (fun a => box a = v)).card ≤ (bohr Γ ρ').card := by
    intro v _
    rcases ((bohr Γ ρ).filter (fun a => box a = v)).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · rw [he]; simp
    · refine card_le_card_of_injOn (fun x => x - x₀) ?_ ?_
      · intro x hx
        rw [mem_coe, mem_filter] at hx
        rw [mem_filter] at hx₀
        rw [mem_coe, mem_bohr]
        intro γ hγ
        have e1 := congrFun hx.2 ⟨γ, hγ⟩
        have e2 := congrFun hx₀.2 ⟨γ, hγ⟩
        have heq : ⌊sc (γ * x) / ρ'⌋ = ⌊sc (γ * x₀) / ρ'⌋ := e1.trans e2.symm
        have := Int.abs_sub_lt_one_of_floor_eq_floor heq
        rw [mul_sub]
        refine (cn_sub_le_abs _ _).trans ?_
        rw [← sub_div, abs_div, abs_of_pos h', div_lt_one h'] at this
        exact this.le
      · intro a _ b _ hab
        simpa using hab
  have hcard := card_le_mul_card_image (bohr Γ ρ) _ hfib
  have hT : ((T.card : ℕ) : ℝ) ≤ (4 * r) ^ Γ.card := by
    rw [Fintype.card_piFinset]
    simp only [prod_const, Finset.card_univ, Fintype.card_coe]
    push_cast
    exact pow_le_pow_left₀ (by positivity) (card_Icc_floor_le hr) _
  have h4 : 4 * ρ / ρ' = 4 * r := by rw [hr_def]; ring
  rw [h4]
  calc ((bohr Γ ρ).card : ℝ) ≤ (bohr Γ ρ').card * ((bohr Γ ρ).image box).card := by
        exact_mod_cast hcard
    _ ≤ (bohr Γ ρ').card * T.card := by
        gcongr
    _ ≤ (bohr Γ ρ').card * (4 * r) ^ Γ.card := by gcongr
    _ = _ := by ring

/-! ### Regularity -/

/-! ### Dilation by a unit -/

end

end KM
end File_KM_Bohr

section File_KM_Conv
/-!
# Convolutions and normalised indicator functions on a finite abelian group
-/

open Finset

namespace KM

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Indicator function of a finset. -/
def ind (S : Finset G) : G → ℝ := fun x => if x ∈ S then 1 else 0

variable {S T A B : Finset G} {f g h : G → ℝ} {x y t : G}

lemma mu_nonneg (S : Finset G) (x : G) : 0 ≤ mu S x := by
  unfold mu; split_ifs <;> positivity

lemma mu_le (S : Finset G) (x : G) : mu S x ≤ (S.card : ℝ)⁻¹ := by
  unfold mu; split_ifs
  · exact le_rfl
  · positivity

lemma mu_eq_inv_mul_ind (S : Finset G) : mu S = fun x => (S.card : ℝ)⁻¹ * ind S x := by
  ext x; unfold mu ind; split_ifs <;> simp

lemma sum_ind (S : Finset G) : ∑ x, ind S x = S.card := by
  unfold ind; rw [sum_ite_mem, univ_inter]; simp

lemma sum_mu (hS : S.Nonempty) : ∑ x, mu S x = 1 := by
  rw [mu_eq_inv_mul_ind]; simp only; rw [← mul_sum, sum_ind]
  have : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  field_simp

/-! ### Reindexing -/

lemma sum_add_right (f : G → ℝ) (t : G) : ∑ x, f (x + t) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)

/-! ### Basic properties of convolutions -/

/-! ### Translates of indicator functions -/

end

end KM
end File_KM_Conv

section File_GT_Bohr
/-!
# Regular probability distributions on Bohr sets (Green–Tao §4)

`regP Γ ρ a = 2 ∫_{1/2}^1 μ_{B(Γ, tρ)}(a) dt`, and the approximate translation invariance
(Lemma 4.4): translating by an element of `B(Γ', ρ')`, `Γ ⊆ Γ'`, changes `regP Γ ρ` by at most
`O(|Γ| ρ'/ρ)` in total variation.
-/

open Finset MeasureTheory KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N]

/-- A bounded measurable real function is interval integrable. -/
lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ t, |f t| ≤ M) (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := M) (by simp) hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hM t

variable (Γ : Finset (ZMod N)) {ρ : ℝ}

lemma bohr_mul_mono (hρ : 0 ≤ ρ) : Monotone fun t : ℝ => bohr Γ (t * ρ) :=
  fun _ _ h => bohr_mono (mul_le_mul_of_nonneg_right h hρ)

lemma card_bohr_mul_mono (hρ : 0 ≤ ρ) :
    Monotone fun t : ℝ => ((bohr Γ (t * ρ)).card : ℝ) :=
  fun s t h => by
    try simp only
    exact_mod_cast card_le_card (bohr_mul_mono Γ hρ h)

lemma measurable_mu_bohr (hρ : 0 ≤ ρ) (a : ZMod N) :
    Measurable fun t : ℝ => mu (bohr Γ (t * ρ)) a := by
  have h1 : Measurable fun t : ℝ => ((bohr Γ (t * ρ)).card : ℝ)⁻¹ :=
    (card_bohr_mul_mono Γ hρ).measurable.inv
  have h2 : Measurable fun t : ℝ => KM.ind (bohr Γ (t * ρ)) a := by
    apply Monotone.measurable
    intro s t hst
    simp only [KM.ind]
    by_cases hs : a ∈ bohr Γ (s * ρ)
    · rw [if_pos hs, if_pos (bohr_mul_mono Γ hρ hst hs)]
    · rw [if_neg hs]; split_ifs <;> norm_num
  have e : (fun t : ℝ => mu (bohr Γ (t * ρ)) a) =
      fun t => ((bohr Γ (t * ρ)).card : ℝ)⁻¹ * KM.ind (bohr Γ (t * ρ)) a := by
    funext t; rw [mu_eq_inv_mul_ind]
  rw [e]; exact h1.mul h2

lemma abs_mu_le_one (S : Finset (ZMod N)) (a : ZMod N) : |mu S a| ≤ 1 := by
  rw [abs_of_nonneg (mu_nonneg S a)]
  refine (mu_le S a).trans ?_
  rcases Nat.eq_zero_or_pos S.card with h | h
  · simp [h]
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast h)

lemma intervalIntegrable_mu_bohr (hρ : 0 ≤ ρ) (a : ZMod N) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => mu (bohr Γ (t * ρ)) a) volume x y :=
  intervalIntegrable_of_bdd (measurable_mu_bohr Γ hρ a) (fun _ => abs_mu_le_one _ a) x y

lemma regP_nonneg (a : ZMod N) : 0 ≤ regP Γ ρ a := by
  unfold regP
  have := intervalIntegral.integral_nonneg (a := (1 / 2 : ℝ)) (b := 1) (μ := volume)
    (f := fun t => mu (bohr Γ (t * ρ)) a) (by norm_num) (fun t _ => mu_nonneg _ a)
  linarith

lemma sum_regP (hρ : 0 ≤ ρ) : ∑ a, regP Γ ρ a = 1 := by
  unfold regP
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum
    (fun a _ => intervalIntegrable_mu_bohr Γ hρ a _ _)]
  have : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, ∑ a, mu (bohr Γ (t * ρ)) a = 1 := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [Set.uIcc_of_le (by norm_num)] at ht; linarith [ht.1]
    exact sum_mu (bohr_nonempty (mul_nonneg ht0 hρ))
  rw [intervalIntegral.integral_congr this]
  simp; norm_num

/-- `L(s) = log |B(Γ, s)|`. -/
def logCard (s : ℝ) : ℝ := Real.log (bohr Γ s).card

lemma logCard_mono : Monotone (logCard Γ) := by
  intro s t hst
  unfold logCard
  have hc : (bohr Γ s).card ≤ (bohr Γ t).card := card_le_card (bohr_mono hst)
  rcases Nat.eq_zero_or_pos (bohr Γ s).card with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hc)

lemma min_two_le_four_log {X : ℝ} (hX : 1 ≤ X) : min 2 (X - 1) ≤ 4 * Real.log X := by
  rcases le_or_gt X 2 with h | h
  · have h1 : (X - 1) / X ≤ Real.log X := by
      have := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < X)
      have e : (X - 1) / X = 1 - X⁻¹ := by field_simp
      rw [e]; exact this
    have h2 : (X - 1) / 2 ≤ (X - 1) / X := div_le_div_of_nonneg_left (by linarith) (by linarith) h
    exact (min_le_right _ _).trans (by linarith)
  · have h1 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) h.le
    have h2 := Real.log_two_gt_d9
    exact (min_le_left _ _).trans (by linarith)

variable {Γ} in
/-- Pointwise total variation bound for a single Bohr set. -/
lemma tv_mu_translate {Γ' : Finset (ZMod N)} (hΓ : Γ ⊆ Γ') {ρ' s : ℝ} (hρ' : 0 ≤ ρ')
    {h : ZMod N} (hh : h ∈ bohr Γ' ρ') (hs : ρ' ≤ s) :
    ∑ a, |mu (bohr Γ s) (a + h) - mu (bohr Γ s) a| ≤
      4 * (logCard Γ (s + ρ') - logCard Γ (s - ρ')) := by
  have hh' : h ∈ bohr Γ ρ' := bohr_anti hΓ hh
  set B := bohr Γ s with hB
  set Bp := bohr Γ (s + ρ') with hBp
  set Bm := bohr Γ (s - ρ') with hBm
  have hBm0 : 0 < Bm.card := bohr_card_pos (by linarith)
  have hBmB : Bm.card ≤ B.card := card_le_card (bohr_mono (by linarith))
  have hBBp : B.card ≤ Bp.card := card_le_card (bohr_mono (by linarith))
  have hBmBp : Bm.card ≤ Bp.card := hBmB.trans hBBp
  have hBmr : (0 : ℝ) < Bm.card := by exact_mod_cast hBm0
  have hBr : (0 : ℝ) < B.card := by exact_mod_cast hBm0.trans_le hBmB
  -- pointwise indicator bound
  have hind : ∀ a, |KM.ind B (a + h) - KM.ind B a| ≤ KM.ind Bp a - KM.ind Bm a := by
    intro a
    by_cases ham : a ∈ Bm
    · have ha : a ∈ B := bohr_mono (by linarith) ham
      have hah : a + h ∈ B := by
        have := add_mem_bohr ham hh'
        exact bohr_mono (by linarith) this
      have hap : a ∈ Bp := bohr_mono (by linarith) ham
      simp [KM.ind, ha, hah, hap, ham]
    · by_cases hap : a ∈ Bp
      · have h1 : |KM.ind B (a + h) - KM.ind B a| ≤ 1 := by
          unfold KM.ind; split_ifs <;> norm_num
        simpa [KM.ind, hap, ham] using h1
      · have ha : a ∉ B := fun h' => hap (bohr_mono (by linarith) h')
        have hah : a + h ∉ B := by
          intro h'
          apply hap
          have := sub_mem_bohr h' hh'
          rw [add_sub_cancel_right] at this
          exact bohr_mono (by linarith) this
        simp [KM.ind, ha, hah, hap, ham]
  have hmu : ∀ x, mu B x = (B.card : ℝ)⁻¹ * KM.ind B x := fun x => by rw [mu_eq_inv_mul_ind]
  have hsum1 : ∑ a, |mu B (a + h) - mu B a| ≤ ((Bp.card : ℝ) - Bm.card) / Bm.card := by
    calc ∑ a, |mu B (a + h) - mu B a|
        = ∑ a, (B.card : ℝ)⁻¹ * |KM.ind B (a + h) - KM.ind B a| := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hmu, hmu, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hBr)]
      _ ≤ ∑ a, (B.card : ℝ)⁻¹ * (KM.ind Bp a - KM.ind Bm a) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hind a) (by positivity)
      _ = ((Bp.card : ℝ) - Bm.card) / B.card := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_ind, sum_ind, div_eq_inv_mul]
      _ ≤ ((Bp.card : ℝ) - Bm.card) / Bm.card := by
          apply div_le_div_of_nonneg_left _ hBmr (by exact_mod_cast hBmB)
          have : (Bm.card : ℝ) ≤ Bp.card := by exact_mod_cast hBmBp
          linarith
  have hsum2 : ∑ a, |mu B (a + h) - mu B a| ≤ 2 := by
    calc ∑ a, |mu B (a + h) - mu B a| ≤ ∑ a, (mu B (a + h) + mu B a) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [abs_le]; constructor <;> linarith [mu_nonneg B (a + h), mu_nonneg B a]
      _ = 2 := by
          rw [Finset.sum_add_distrib, sum_add_right (mu B) h, sum_mu (bohr_nonempty (by linarith))]
          norm_num
  have hX : 1 ≤ (Bp.card : ℝ) / Bm.card := by
    rw [le_div_iff₀ hBmr, one_mul]; exact_mod_cast hBmBp
  have hmin := min_two_le_four_log hX
  have e1 : ((Bp.card : ℝ) - Bm.card) / Bm.card = (Bp.card : ℝ) / Bm.card - 1 := by
    rw [sub_div, div_self hBmr.ne']
  have e2 : Real.log ((Bp.card : ℝ) / Bm.card) = logCard Γ (s + ρ') - logCard Γ (s - ρ') := by
    unfold logCard
    rw [Real.log_div (by exact_mod_cast (hBm0.trans_le hBmBp).ne') hBmr.ne']
  rw [e2, ← e1] at hmin
  exact (le_min hsum2 hsum1).trans hmin

lemma logCard_mul_mono (hρ : 0 ≤ ρ) : Monotone fun t : ℝ => logCard Γ (t * ρ) :=
  fun _ _ h => logCard_mono Γ (mul_le_mul_of_nonneg_right h hρ)

lemma intervalIntegrable_logCard_mul (hρ : 0 ≤ ρ) (c : ℝ) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => logCard Γ (t * ρ + c)) volume x y := by
  apply Monotone.intervalIntegrable
  intro s t h
  exact logCard_mono Γ (by nlinarith)

/-- The telescoping estimate in the proof of Lemma 4.4. -/
lemma integral_logCard_diff_le (hρ : 0 < ρ) {ρ' : ℝ} (hρ' : 0 ≤ ρ') (h4 : 4 * ρ' ≤ ρ) :
    ∫ t in (1 / 2 : ℝ)..1, (logCard Γ (t * ρ + ρ') - logCard Γ (t * ρ + -ρ')) ≤
      2 * (ρ' / ρ) * (logCard Γ (ρ + ρ') - logCard Γ (ρ / 2 - ρ')) := by
  set δ := ρ' / ρ with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hρ' hρ.le
  have hδ4 : δ ≤ 1 / 4 := by rw [hδ, div_le_iff₀ hρ]; linarith
  set M : ℝ → ℝ := fun t => logCard Γ (t * ρ) with hM
  have hMm : Monotone M := logCard_mul_mono Γ hρ.le
  have hMi : ∀ x y, IntervalIntegrable M volume x y := fun x y => hMm.intervalIntegrable
  have e1 : ∀ t, logCard Γ (t * ρ + ρ') = M (t + δ) := by
    intro t; simp only [hM, hδ]; congr 1; field_simp
  have e2 : ∀ t, logCard Γ (t * ρ + -ρ') = M (t + -δ) := by
    intro t; simp only [hM, hδ]; congr 1; field_simp
  simp_rw [e1, e2]
  have m1 : Monotone fun t => M (t + δ) := hMm.comp fun a b h => by linarith
  have m2 : Monotone fun t => M (t + -δ) := hMm.comp fun a b h => by linarith
  rw [intervalIntegral.integral_sub m1.intervalIntegrable m2.intervalIntegrable,
    intervalIntegral.integral_comp_add_right M δ, intervalIntegral.integral_comp_add_right M (-δ)]
  -- split the intervals
  have s1 := intervalIntegral.integral_add_adjacent_intervals (hMi (1 / 2 + δ) (1 + -δ))
    (hMi (1 + -δ) (1 + δ))
  have s2 := intervalIntegral.integral_add_adjacent_intervals (hMi (1 / 2 + -δ) (1 / 2 + δ))
    (hMi (1 / 2 + δ) (1 + -δ))
  have b1 : ∫ t in (1 + -δ)..(1 + δ), M t ≤ ∫ t in (1 + -δ)..(1 + δ), M (1 + δ) :=
    intervalIntegral.integral_mono_on (by linarith) (hMi _ _) intervalIntegrable_const
      fun t ht => hMm ht.2
  have b2 : ∫ t in (1 / 2 + -δ)..(1 / 2 + δ), M (1 / 2 + -δ) ≤
      ∫ t in (1 / 2 + -δ)..(1 / 2 + δ), M t :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hMi _ _)
      fun t ht => hMm ht.1
  rw [intervalIntegral.integral_const, smul_eq_mul] at b1 b2
  have e3 : M (1 + δ) = logCard Γ (ρ + ρ') := by
    simp only [hM, hδ]; congr 1; field_simp
  have e4 : M (1 / 2 + -δ) = logCard Γ (ρ / 2 - ρ') := by
    simp only [hM, hδ]; congr 1; field_simp; ring
  rw [e3] at b1; rw [e4] at b2
  nlinarith

lemma log_twenty_lt_three : Real.log 20 < 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [sq_nonneg (Real.exp 1)]

lemma logCard_ratio_le (hρ : 0 < ρ) {ρ' : ℝ} (hρ' : 0 ≤ ρ') (h4 : 4 * ρ' ≤ ρ) :
    logCard Γ (ρ + ρ') - logCard Γ (ρ / 2 - ρ') ≤ Γ.card * Real.log 20 := by
  have hpos : 0 < ρ / 2 - ρ' := by linarith
  have hc := card_bohr_le Γ hpos (by linarith : ρ / 2 - ρ' ≤ ρ + ρ')
  have hr : 4 * (ρ + ρ') / (ρ / 2 - ρ') ≤ 20 := by
    rw [div_le_iff₀ hpos]; linarith
  have hm0 : (0 : ℝ) < (bohr Γ (ρ / 2 - ρ')).card := by exact_mod_cast bohr_card_pos hpos.le
  have hc' : ((bohr Γ (ρ + ρ')).card : ℝ) ≤ 20 ^ Γ.card * (bohr Γ (ρ / 2 - ρ')).card :=
    hc.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr _) hm0.le)
  unfold logCard
  have hp0 : (0 : ℝ) < (bohr Γ (ρ + ρ')).card := by exact_mod_cast bohr_card_pos (by linarith)
  have := Real.log_le_log hp0 hc'
  rw [Real.log_mul (by positivity) hm0.ne', Real.log_pow] at this
  linarith

variable {Γ} in
/-- **Approximate translation invariance** (Green–Tao, Lemma 4.4(i)): if `Γ ⊆ Γ'` and
`h ∈ B(Γ', ρ')` with `4ρ' ≤ ρ`, then `regP Γ ρ` and its translate by `h` differ in total variation
by at most `50 |Γ| ρ'/ρ`. -/
theorem regP_tv {Γ' : Finset (ZMod N)} (hΓ : Γ ⊆ Γ') (hρ : 0 < ρ) {ρ' : ℝ} (hρ' : 0 ≤ ρ')
    (h4 : 4 * ρ' ≤ ρ) {h : ZMod N} (hh : h ∈ bohr Γ' ρ') :
    ∑ a, |regP Γ ρ (a + h) - regP Γ ρ a| ≤ 50 * Γ.card * ρ' / ρ := by
  set g : ZMod N → ℝ → ℝ := fun a t => mu (bohr Γ (t * ρ)) (a + h) - mu (bohr Γ (t * ρ)) a
    with hg
  have hgi : ∀ a, IntervalIntegrable (g a) volume (1 / 2) 1 := fun a =>
    (intervalIntegrable_mu_bohr Γ hρ.le _ _ _).sub (intervalIntegrable_mu_bohr Γ hρ.le _ _ _)
  have hgm : ∀ a, Measurable (g a) := fun a =>
    (measurable_mu_bohr Γ hρ.le _).sub (measurable_mu_bohr Γ hρ.le _)
  have hgai : ∀ a, IntervalIntegrable (fun t => |g a t|) volume (1 / 2) 1 := fun a =>
    intervalIntegrable_of_bdd (hgm a).abs (M := 2) (fun t => by
      rw [abs_abs]
      have h1 := abs_mu_le_one (bohr Γ (t * ρ)) (a + h)
      have h2 := abs_mu_le_one (bohr Γ (t * ρ)) a
      calc |g a t| ≤ |mu (bohr Γ (t * ρ)) (a + h)| + |mu (bohr Γ (t * ρ)) a| := abs_sub _ _
        _ ≤ 2 := by linarith) _ _
  have step1 : ∀ a, |regP Γ ρ (a + h) - regP Γ ρ a| ≤ 2 * ∫ t in (1 / 2 : ℝ)..1, |g a t| := by
    intro a
    have e : regP Γ ρ (a + h) - regP Γ ρ a = 2 * ∫ t in (1 / 2 : ℝ)..1, g a t := by
      unfold regP
      rw [← mul_sub, ← intervalIntegral.integral_sub (intervalIntegrable_mu_bohr Γ hρ.le _ _ _)
        (intervalIntegrable_mu_bohr Γ hρ.le _ _ _)]
    rw [e, abs_mul, abs_two]
    have := intervalIntegral.norm_integral_le_integral_norm (f := g a) (μ := volume)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    simp only [Real.norm_eq_abs] at this
    linarith
  have step2 : ∑ a, ∫ t in (1 / 2 : ℝ)..1, |g a t| ≤
      ∫ t in (1 / 2 : ℝ)..1, 4 * (logCard Γ (t * ρ + ρ') - logCard Γ (t * ρ + -ρ')) := by
    rw [← intervalIntegral.integral_finset_sum fun a _ => hgai a]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · have := IntervalIntegrable.sum Finset.univ fun a _ => hgai a
      simpa only [Finset.sum_fn] using this
    · exact ((intervalIntegrable_logCard_mul Γ hρ.le _ _ _).sub
        (intervalIntegrable_logCard_mul Γ hρ.le _ _ _)).const_mul 4
    · intro t ht
      have ht1 : ρ' ≤ t * ρ := by nlinarith [ht.1]
      have := tv_mu_translate hΓ hρ' hh ht1
      simpa [hg, sub_eq_add_neg] using this
  have step3 := integral_logCard_diff_le Γ hρ hρ' h4
  have step4 := logCard_ratio_le Γ hρ hρ' h4
  have hl := log_twenty_lt_three
  rw [intervalIntegral.integral_const_mul] at step2
  have hδ0 : 0 ≤ ρ' / ρ := div_nonneg hρ' hρ.le
  have hcard : (0 : ℝ) ≤ Γ.card := Nat.cast_nonneg _
  calc ∑ a, |regP Γ ρ (a + h) - regP Γ ρ a| ≤ ∑ a, 2 * ∫ t in (1 / 2 : ℝ)..1, |g a t| :=
        Finset.sum_le_sum fun a _ => step1 a
    _ = 2 * ∑ a, ∫ t in (1 / 2 : ℝ)..1, |g a t| := by rw [Finset.mul_sum]
    _ ≤ 2 * (4 * (2 * (ρ' / ρ) * (Γ.card * Real.log 20))) := by
        have := mul_le_mul_of_nonneg_left step4 (by positivity : (0 : ℝ) ≤ 2 * (ρ' / ρ))
        nlinarith
    _ ≤ 50 * Γ.card * ρ' / ρ := by
        rw [mul_div_assoc]
        have : Γ.card * Real.log 20 * (ρ' / ρ) ≤ Γ.card * 3 * (ρ' / ρ) := by
          apply mul_le_mul_of_nonneg_right _ hδ0
          exact mul_le_mul_of_nonneg_left hl.le hcard
        nlinarith

end

end GT
end File_GT_Bohr

section File_GT_LocU2
/-!
# The local inverse `U²` theorem (Green–Tao, Theorem 4.10)

We prove the local inverse theorem for the Gowers `U²` norm in the general form: if `P₀, P₁` are
probability distributions on `ZMod N` such that `P₀` is almost invariant under translation by
elements of the support of `P₁` (in total variation, up to `ε`), and a `1`-bounded `f` has
local `U²`-type average at least `η` with `144 ε ≤ η²`, then `f` correlates with a linear phase
on translates of `P₁`.  The proof (due to F. Shao) replaces `P₀` by products of square roots
and then uses Fourier analysis on `ZMod N`.
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N]

/-! ### Fourier identities -/

/-! ### Elementary estimates -/

lemma sum_shift' {M : Type*} [AddCommMonoid M] (F : ZMod N → M) (t : ZMod N) :
    ∑ x, F (x + t) = ∑ x, F x :=
  Fintype.sum_equiv (Equiv.addRight t) _ _ fun _ => rfl

section dist

variable {P : ZMod N → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
include hP hP1

end dist

/-! ### The main estimates -/

section main

end main

end

end GT
end File_GT_LocU2

section File_GT_WeylTorus
/-!
# The Weyl lemma on a torus `(ℝ/ℤ)^κ`

A function `F` on `(ℝ/ℤ)^κ` which is Lipschitz with coordinate weights `w`, bounded by `B`
and of mean zero on the grid `((1/N)ℤ/ℤ)^κ`, and has a large weighted average over some points
`ξⱼ`, correlates on those points with a non-zero character `e(k·x)` with `|kᵢ| < 2Mᵢ`,
provided `∑ wᵢ/Mᵢ < δ/4` and `N` is large enough.
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

lemma coe_sum_real {κ : Type*} (s : Finset κ) (f : κ → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : UnitAddCircle) = ∑ i ∈ s, (f i : UnitAddCircle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, AddCircle.coe_add, ih]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

variable {N : ℕ} [NeZero N]

end

end GT
end File_GT_WeylTorus

section File_GT_Prob
/-!
# Common toolkit for the Green–Tao argument

* the exponential `e(x)` of a point of `ℝ/ℤ`, with the bounds `4‖x‖ ≤ |e(x) - 1| ≤ 2π‖x‖`;
* the dual norm `‖h‖_{S^⊥}` (`snorm`) and its relation with Bohr sets;
* support and translation properties of the regular distributions `regP`;
* the local inverse `U²` theorem for regular distributions on Bohr sets.
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

/-! ### The exponential on `ℝ/ℤ` -/

variable {N : ℕ} [NeZero N]

/-! ### The dual norm `‖h‖_{S^⊥}` -/

variable {S : Finset (ZMod N)}

lemma snorm_nonneg (h : ZMod N) : 0 ≤ snorm S h := by
  unfold snorm
  split_ifs with hS
  · obtain ⟨s, hs⟩ := hS
    exact (cn_nonneg _).trans (Finset.le_sup' (fun s => cn (s * h)) hs)
  · exact le_rfl

lemma cn_le_snorm {s : ZMod N} (hs : s ∈ S) (h : ZMod N) : cn (s * h) ≤ snorm S h := by
  unfold snorm
  rw [dif_pos ⟨s, hs⟩]
  exact Finset.le_sup' (fun s => cn (s * h)) hs

lemma snorm_le_iff {h : ZMod N} {ρ : ℝ} (hρ : 0 ≤ ρ) : snorm S h ≤ ρ ↔ ∀ s ∈ S, cn (s * h) ≤ ρ := by
  constructor
  · intro H s hs; exact (cn_le_snorm hs h).trans H
  · intro H
    unfold snorm
    split_ifs with hS
    · exact Finset.sup'_le hS _ H
    · exact hρ

lemma mem_bohr_iff_snorm {h : ZMod N} {ρ : ℝ} (hρ : 0 ≤ ρ) : h ∈ bohr S ρ ↔ snorm S h ≤ ρ := by
  rw [mem_bohr, snorm_le_iff hρ]

lemma snorm_le_of_mem {h : ZMod N} {ρ : ℝ} (hh : h ∈ bohr S ρ) (hρ : 0 ≤ ρ) : snorm S h ≤ ρ :=
  (mem_bohr_iff_snorm hρ).mp hh

lemma snorm_add_le (h k : ZMod N) : snorm S (h + k) ≤ snorm S h + snorm S k := by
  rw [snorm_le_iff (add_nonneg (snorm_nonneg _) (snorm_nonneg _))]
  intro s hs
  rw [mul_add]
  exact (cn_add_le _ _).trans (add_le_add (cn_le_snorm hs h) (cn_le_snorm hs k))

lemma snorm_nsmul_le (n : ℕ) (h : ZMod N) : snorm S ((n : ZMod N) * h) ≤ n * snorm S h := by
  rw [snorm_le_iff (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (snorm_nonneg h))]
  intro s hs
  rw [mul_left_comm]
  exact (cn_natCast_mul_le n _).trans
    (mul_le_mul_of_nonneg_left (cn_le_snorm hs h) (Nat.cast_nonneg (α := ℝ) n))

lemma snorm_mono {S' : Finset (ZMod N)} (hSS : S ⊆ S') (h : ZMod N) : snorm S h ≤ snorm S' h := by
  rw [snorm_le_iff (snorm_nonneg _)]
  exact fun s hs => cn_le_snorm (hSS hs) h

/-! ### Regular distributions -/

lemma regP_eq_zero_of_not_mem {Γ : Finset (ZMod N)} {ρ : ℝ} (hρ : 0 ≤ ρ) {a : ZMod N}
    (ha : a ∉ bohr Γ ρ) : regP Γ ρ a = 0 := by
  unfold regP
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero,
    mul_zero]
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
  try simp only
  have : a ∉ bohr Γ (t * ρ) := fun h' =>
    ha (bohr_mono (by nlinarith [ht.2] : t * ρ ≤ ρ) h')
  simp [mu, this]

lemma mem_bohr_of_regP_ne_zero {Γ : Finset (ZMod N)} {ρ : ℝ} (hρ : 0 ≤ ρ) {a : ZMod N}
    (ha : regP Γ ρ a ≠ 0) : a ∈ bohr Γ ρ := by
  by_contra h; exact ha (regP_eq_zero_of_not_mem hρ h)

/-- Translation estimate in the form used throughout: for `|G| ≤ B`, shifting the argument of
a regular distribution by `h ∈ B(Γ', ρ')` changes the average by at most `B · 50|Γ|ρ'/ρ`. -/
lemma regP_shift {Γ Γ' : Finset (ZMod N)} (hΓ : Γ ⊆ Γ') {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 ≤ ρ')
    (h4 : 4 * ρ' ≤ ρ) {h : ZMod N} (hh : h ∈ bohr Γ' ρ') {B : ℝ} (G : ZMod N → ℂ)
    (hG : ∀ x, ‖G x‖ ≤ B) :
    ‖∑ x, (regP Γ ρ x : ℂ) * G (x + h) - ∑ x, (regP Γ ρ x : ℂ) * G x‖ ≤
      B * (50 * Γ.card * ρ' / ρ) := by
  have e : ∑ x, (regP Γ ρ x : ℂ) * G (x + h) = ∑ x, (regP Γ ρ (x + -h) : ℂ) * G x := by
    rw [← sum_shift' (fun x => (regP Γ ρ (x + -h) : ℂ) * G x) h]
    simp
  rw [e, ← sum_sub_distrib]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hG 0)
  calc ‖∑ x, ((regP Γ ρ (x + -h) : ℂ) * G x - (regP Γ ρ x : ℂ) * G x)‖
      ≤ ∑ x, |regP Γ ρ (x + -h) - regP Γ ρ x| * B := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
        rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hG x) (abs_nonneg _)
    _ = B * ∑ x, |regP Γ ρ (x + -h) - regP Γ ρ x| := by rw [← sum_mul, mul_comm]
    _ ≤ B * (50 * Γ.card * ρ' / ρ) :=
        mul_le_mul_of_nonneg_left (regP_tv hΓ hρ hρ' h4 (neg_mem_bohr hh)) hB

/-! ### Averages against probability vectors -/

section avg

variable {α : Type*} [Fintype α] {P : α → ℝ}

end avg

end

end GT
end File_GT_Prob

section File_GT_LocQ
/-!
# Calculus of locally quadratic maps on shifted Bohr sets

For `Ξ` locally quadratic on `n₀ + B(S, ρ)` we study the second difference
`D2 Ξ a h k = Ξ(a+h+k) - Ξ(a+h) - Ξ(a+k) + Ξ(a)`: it does not depend on the base point and is
additive in each variable (under `S^⊥`-norm budgets).
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p] {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M]

lemma mem_sBohr {n0 x : ZMod p} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    x ∈ sBohr S n0 ρ ↔ snorm S (x - n0) ≤ ρ := by
  rw [sBohr, Set.mem_setOf_eq, mem_bohr_iff_snorm hρ]

lemma LocQuad.comp {B : Set (ZMod p)} {Ξ : ZMod p → M} (hL : LocQuad B Ξ)
    {M' : Type*} [AddCommGroup M'] (f : M →+ M') : LocQuad B (fun x => f (Ξ x)) := by
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have := hL n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have e := congrArg f this
  simp only [map_add, map_sub, map_zero] at e
  exact e

variable {n0 : ZMod p} {ρ : ℝ} {Ξ : ZMod p → M}

end

end GT
end File_GT_LocQ

section File_GT_WD
/-!
# Weyl differencing for locally quadratic phases (Green–Tao §7)
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- Reindexing the shifted regular distribution `a ↦ P(a - n₀)`. -/
lemma sum_regP_shift_center {S : Finset (ZMod p)} {ρ : ℝ} (n0 : ZMod p) {M : Type*}
    [AddCommMonoid M] (f : ZMod p → ℝ → M) :
    ∑ a, f a (regP S ρ (a - n0)) = ∑ x, f (x + n0) (regP S ρ x) := by
  rw [← sum_shift' (fun a => f a (regP S ρ (a - n0))) n0]
  simp

lemma sum_regP_center (S : Finset (ZMod p)) {ρ : ℝ} (hρ : 0 ≤ ρ) (n0 : ZMod p) :
    ∑ a, regP S ρ (a - n0) = 1 := by
  rw [sum_regP_shift_center (S := S) (ρ := ρ) n0 (fun _ w => w)]
  exact sum_regP S hρ

end

end GT
end File_GT_WD

section File_GT_MixTV
/-!
# Total variation of a mixture of small translates

If `a` is drawn regularly from `n₀ + B(S, ρ/2)`, `t` regularly from `B(S, σ)` and then `y` from a
distribution `Q_a` (which may depend on `a`) supported in `B(S, ρ_q)`, then `a + t + y` is
close in total variation to `a`.
-/

open Finset KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N]

/-- Real-valued version of `regP_shift`. -/
lemma regP_shift_real {Γ Γ' : Finset (ZMod N)} (hΓ : Γ ⊆ Γ') {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hρ' : 0 ≤ ρ') (h4 : 4 * ρ' ≤ ρ) {h : ZMod N} (hh : h ∈ bohr Γ' ρ') {B : ℝ}
    (g : ZMod N → ℝ) (hg : ∀ x, |g x| ≤ B) :
    |∑ x, regP Γ ρ x * g (x + h) - ∑ x, regP Γ ρ x * g x| ≤ B * (50 * Γ.card * ρ' / ρ) := by
  have := regP_shift hΓ hρ hρ' h4 hh (fun x => (g x : ℂ)) (fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hg x)
  have e : ∑ x, (regP Γ ρ x : ℂ) * (g (x + h) : ℂ) - ∑ x, (regP Γ ρ x : ℂ) * (g x : ℂ) =
      ((∑ x, regP Γ ρ x * g (x + h) - ∑ x, regP Γ ρ x * g x : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

/-- Averages of bounded quantities stay bounded. -/
lemma abs_wavg_le {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (F : α → ℝ) {B : ℝ} (hF : ∀ x, P x ≠ 0 → |F x| ≤ B) : |∑ x, P x * F x| ≤ B := by
  calc |∑ x, P x * F x| ≤ ∑ x, P x * B := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hP x)]
        by_cases hx : P x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_left (hF x hx) (hP x)
    _ = B := by rw [← sum_mul, hP1, one_mul]

variable {p : ℕ} [NeZero p]

set_option maxHeartbeats 1000000 in
/-- **Mixtures of small translates.** -/
theorem tv_mix {S : Finset (ZMod p)} {n0 : ZMod p} {ρ σ ρq : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hq : 0 ≤ ρq) (h4q : 4 * ρq ≤ σ) (h4σ : 4 * σ ≤ ρ / 2) (Q : ZMod p → ZMod p → ℝ)
    (hQ0 : ∀ a y, 0 ≤ Q a y) (hQ1 : ∀ a, ∑ y, Q a y = 1)
    (hQs : ∀ a y, Q a y ≠ 0 → snorm S y ≤ ρq) (g : ZMod p → ℝ) {B : ℝ}
    (hg : ∀ x, |g x| ≤ B) :
    |∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) -
        ∑ x, regP S (ρ / 2) (x - n0) * g x| ≤
      B * (50 * S.card * ρq / σ) + B * (50 * S.card * σ / (ρ / 2)) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg 0)
  have hP0 : ∀ a, 0 ≤ regP S (ρ / 2) (a - n0) := fun a => regP_nonneg _ _
  have hP1 : ∑ a, regP S (ρ / 2) (a - n0) = 1 := sum_regP_center S (by positivity) n0
  have hU0 : ∀ t, 0 ≤ regP S σ t := fun t => regP_nonneg _ _
  have hU1 : ∑ t, regP S σ t = 1 := sum_regP S hσ.le
  -- step 1: removing `y`
  have step1 : ∀ a, |∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) -
      ∑ t, regP S σ t * g (a + t)| ≤ B * (50 * S.card * ρq / σ) := by
    intro a
    have e1 : ∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) =
        ∑ y, Q a y * ∑ t, regP S σ t * g (a + (t + y)) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun y _ => sum_congr rfl fun t _ => ?_
      rw [add_assoc]; ring
    have e2 : ∑ t, regP S σ t * g (a + t) = ∑ y, Q a y * ∑ t, regP S σ t * g (a + t) := by
      rw [← sum_mul, hQ1, one_mul]
    rw [e1, e2, ← sum_sub_distrib]
    simp_rw [← mul_sub]
    refine abs_wavg_le (hQ0 a) (hQ1 a) _ fun y hy => ?_
    have hyb : y ∈ bohr S ρq := (mem_bohr_iff_snorm hq).mpr (hQs a y hy)
    exact regP_shift_real subset_rfl hσ hq h4q hyb (fun t => g (a + t)) (fun x => hg _)
  -- step 2: removing `t`
  have step2 : |∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t) -
      ∑ x, regP S (ρ / 2) (x - n0) * g x| ≤ B * (50 * S.card * σ / (ρ / 2)) := by
    have e1 : ∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t) =
        ∑ t, regP S σ t * ∑ x, regP S (ρ / 2) x * g (x + t + n0) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun t _ => ?_
      rw [sum_regP_shift_center (S := S) (ρ := ρ / 2) n0
        (fun a w => w * (regP S σ t * g (a + t)))]
      refine sum_congr rfl fun x _ => ?_
      rw [add_right_comm]; ring
    have e2 : ∑ x, regP S (ρ / 2) (x - n0) * g x =
        ∑ t, regP S σ t * ∑ x, regP S (ρ / 2) x * g (x + n0) := by
      rw [← sum_mul, hU1, one_mul]
      exact sum_regP_shift_center (S := S) (ρ := ρ / 2) n0 (fun a w => w * g a)
    rw [e1, e2, ← sum_sub_distrib]
    simp_rw [← mul_sub]
    refine abs_wavg_le hU0 hU1 _ fun t ht => ?_
    have htb : t ∈ bohr S σ := mem_bohr_of_regP_ne_zero hσ.le ht
    have := regP_shift_real subset_rfl (by positivity : (0 : ℝ) < ρ / 2) hσ.le h4σ htb
      (fun x => g (x + n0)) (fun x => hg _)
    refine le_trans (le_of_eq ?_) this
    congr 2
  -- combine
  have hcomb : |∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) -
      ∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t)| ≤
      B * (50 * S.card * ρq / σ) := by
    rw [← sum_sub_distrib]
    simp_rw [← mul_sub]
    exact abs_wavg_le hP0 hP1 _ fun a _ => step1 a
  calc _ = |(∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) -
        ∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t)) +
        (∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t) -
        ∑ x, regP S (ρ / 2) (x - n0) * g x)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hcomb step2)

end

end GT
end File_GT_MixTV

section File_GT_Subtorus
/-!
# Subtori of lattice tori (replacement for Green–Tao, Theorem 5.1)

For a primitive frequency `k ∈ ℤ^d` of a lattice torus `G`, the subtorus `k^⊥` is again a
lattice torus `G.sub B` (with basis given by an integer matrix `B`), and there is a projection
`π` with `y = ι(π y) + (k·y) u` for a fixed integer vector `u` with `k·u = 1`.
-/

open Finset Matrix

namespace GT

noncomputable section

lemma zmap_apply {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) (x : Fin b → UnitAddCircle) (j : Fin a) :
    zmap M x j = ∑ i, M j i • x i := rfl

lemma zmap_coe {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) (t : Fin b → ℝ) :
    zmap M (fun i => (t i : UnitAddCircle)) = fun j => ((∑ i, (M j i : ℝ) * t i : ℝ) : UnitAddCircle) := by
  funext j
  rw [zmap_apply, coe_sum_real]
  refine sum_congr rfl fun i _ => ?_
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]

namespace DTorus

lemma sub_emb (G : DTorus) {d' : ℕ} (B : Matrix (Fin d') (Fin G.d) ℤ) (t : Fin d' → ℝ) :
    (G.sub B).emb t = G.emb (fun i => ∑ j, (B j i : ℝ) * t j) := by
  show ∑ i, t i • zmix B G.v i = ∑ i, (∑ j, (B j i : ℝ) * t j) • G.v i
  simp only [zmix, zvec, Finset.smul_sum, smul_smul, sum_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring_nf

lemma exists_lift {d : ℕ} (c : Fin d → UnitAddCircle) :
    ∃ s : Fin d → ℝ, (fun i => (s i : UnitAddCircle)) = c := by
  choose s hs using fun i => QuotientAddGroup.mk_surjective (c i)
  exact ⟨s, funext hs⟩

/-- Restricting a Lipschitz function to a subtorus (and translating) keeps it Lipschitz. -/
lemma isLip_sub {G : DTorus} {F : G.Pt → ℝ} (hF : G.IsLip F) {d' : ℕ}
    (B : Matrix (Fin d') (Fin G.d) ℤ) (c : G.Pt) :
    (G.sub B).IsLip (fun x => F (zmap Bᵀ x + c)) := by
  intro t t'
  obtain ⟨s, rfl⟩ := exists_lift c
  have e : ∀ u : Fin d' → ℝ, zmap Bᵀ ((G.sub B).pt u) + (fun i => (s i : UnitAddCircle)) =
      G.pt (fun i => ∑ j, (B j i : ℝ) * u j + s i) := by
    intro u
    have hu : (G.sub B).pt u = fun j => (u j : UnitAddCircle) := rfl
    rw [hu, zmap_coe]
    funext i
    simp only [pt, Pi.add_apply, AddCircle.coe_add, Matrix.transpose_apply]
  try simp only
  rw [e t, e t']
  refine (hF _ _).trans (le_of_eq ?_)
  rw [sub_emb]
  congr 1
  congr 1
  funext i
  simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]
  ring

end DTorus

section lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end lattice

end

end GT
end File_GT_Subtorus

section File_GT_BadDimData
/-!
# Infrastructure for Theorem 6.7: label data, refined labels, averages
-/

open Finset KM Matrix

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

namespace LData

/-- The average of `g` against the regular distribution on `n + B(S, ρ/2)`. -/
def avg (L : LData p) (g : ZMod p → ℝ) : ℝ := ∑ x, regP L.S (L.ρ / 2) (x - L.n) * g x

end LData

namespace SLA

/-- The energy as an average of label averages. -/
lemma energy_eq (v : SLA p) (η : ℝ) (hη : 0 ≤ eps4 η) (hρ : ∀ c, 0 ≤ v.ρ c)
    (f : ZMod p → ℝ) :
    (v.triple η).energy f =
      ∑ c, v.prob c * (v.ldata c).avg (fun x => (f x - v.F c (v.Ξ c x)) ^ 2) := by
  unfold Triple.energy LData.avg
  refine sum_congr rfl fun c _ => ?_
  congr 1
  simp only [triple, ldata]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  simp_rw [mul_assoc, ← mul_sum]
  congr 1
  rw [← sum_mul, sum_regP _ (mul_nonneg hη (hρ c)), one_mul]

end SLA

/-! ### Locally quadratic maps -/

lemma LocQuad.mono {B B' : Set (ZMod p)} {M : Type*} [AddCommGroup M] {Ξ : ZMod p → M}
    (hL : LocQuad B Ξ) (hB : B' ⊆ B) : LocQuad B' Ξ := by
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  exact hL n h1 h2 h3 (hB m0) (hB m1) (hB m2) (hB m3) (hB m12) (hB m13) (hB m23) (hB m123)

lemma LocQuad.sub_const {B : Set (ZMod p)} {M : Type*} [AddCommGroup M] {Ξ : ZMod p → M}
    (hL : LocQuad B Ξ) (c : M) : LocQuad B (fun x => Ξ x - c) := by
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have := hL n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  beta_reduce
  refine Eq.trans ?_ this
  abel

/-! ### Dilated frequency sets -/

lemma snorm_image_mul (T : Finset (ZMod p)) (c y : ZMod p) :
    snorm (T.image (fun s => s * c)) y = snorm T (c * y) := by
  classical
  have key : ∀ ρ : ℝ, 0 ≤ ρ → (snorm (T.image (fun s => s * c)) y ≤ ρ ↔ snorm T (c * y) ≤ ρ) := by
    intro ρ hρ
    rw [snorm_le_iff hρ, snorm_le_iff hρ]
    constructor
    · intro H s hs
      have := H (s * c) (mem_image_of_mem _ hs)
      rwa [mul_assoc] at this
    · intro H s' hs'
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hs'
      rw [mul_assoc]; exact H s hs
  apply le_antisymm
  · exact (key _ (snorm_nonneg _)).mpr le_rfl
  · exact (key _ (snorm_nonneg _)).mp le_rfl

/-- Dilating the frequencies by `c⁻¹` with `c = k` a natural number: `‖y‖_S ≤ k ‖y‖_{S/k}`. -/
lemma snorm_le_of_image_inv (hp : p.Prime) (T : Finset (ZMod p)) (k : ℕ)
    (hk : (k : ZMod p) ≠ 0) (y : ZMod p) :
    snorm T y ≤ k * snorm (T.image (fun s => s * (k : ZMod p)⁻¹)) y := by
  haveI := Fact.mk hp
  rw [snorm_image_mul]
  have e : y = (k : ZMod p) * ((k : ZMod p)⁻¹ * y) := by
    rw [← mul_assoc, mul_inv_cancel₀ hk, one_mul]
  conv_lhs => rw [e]
  exact snorm_nsmul_le k _

end

end GT
end File_GT_BadDimData

section File_GT_BadDim
/-!
# Theorem 6.7: bad lower bound implies dimension decrement

The refined approximant: every label `c` is replaced by the labels `(c, a, t)`, where `a` is drawn
from `n_c + B(S_c, ρ_c/2)` and `t` from `B(S_c, σ_c)`. For a poorly distributed `c` the label
`(c, a, t)` gets centre `a + t`, the frequencies `(2m)^{-1}(S_c ∪ {ξ_a})`, a tiny radius `τ_c`
and the codimension one subtorus given by Proposition 7.1; otherwise the data of `c` are copied.
-/

open Finset KM Matrix

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

namespace LData

/-- Validity of the data of one label. -/
def OK (L : LData p) : Prop :=
  (∃ s ∈ L.S, s ≠ 0) ∧ (0 < L.ρ ∧ L.ρ ≤ 1) ∧ L.G.IsLip L.F ∧ (∀ x, |L.F x| ≤ 1) ∧
    LocQuad (sBohr L.S L.n L.ρ) L.Ξ ∧ L.G.Good

end LData

namespace SLA

lemma ofData_valid (C : Type) [Fintype C] (prob : C → ℝ) (D : C → LData p)
    (h0 : ∀ c, 0 ≤ prob c) (h1 : ∑ c, prob c = 1) (hD : ∀ c, (D c).OK) :
    (ofData C prob D).Valid :=
  ⟨h0, h1, fun c => (hD c).1, fun c => (hD c).2.1, fun c => (hD c).2.2.1,
    fun c => (hD c).2.2.2.1, fun c => (hD c).2.2.2.2.1, fun c => (hD c).2.2.2.2.2⟩

lemma ldata_OK {v : SLA p} (hv : v.Valid) (c : v.C) : (v.ldata c).OK :=
  ⟨hv.2.2.1 c, hv.2.2.2.1 c, hv.2.2.2.2.1 c, hv.2.2.2.2.2.1 c, hv.2.2.2.2.2.2.1 c,
    hv.2.2.2.2.2.2.2 c⟩

variable (v : SLA p) (η : ℝ)

variable {v η}

lemma rdata_pos {rd : ∀ c, RData p (v.G c)} {c : v.C} {a t : ZMod p} (h : v.Ref η c a t) :
    v.rdata η rd (c, a, t) = (v.ldata c).refine (rd c) a t (v.tau η c) := by
  classical
  unfold rdata; rw [if_pos h]

lemma rdata_neg {rd : ∀ c, RData p (v.G c)} {c : v.C} {a t : ZMod p} (h : ¬ v.Ref η c a t) :
    v.rdata η rd (c, a, t) = v.ldata c := by
  classical
  unfold rdata; rw [if_neg h]

lemma sig_nonneg (hv : v.Valid) (c : v.C) (hη : 0 < η) : 0 ≤ v.sig η c := by
  have := (hv.2.2.2.1 c).1
  unfold sig p71R lqR lqτ p71δ wρh wδ wP eps4
  positivity

lemma rprob_nonneg (hv : v.Valid) (c' : v.C × ZMod p × ZMod p) : 0 ≤ v.rprob η c' :=
  mul_nonneg (mul_nonneg (hv.1 _) (regP_nonneg _ _)) (regP_nonneg _ _)

lemma sum_rprob (hv : v.Valid) (hη : 0 < η) : ∑ c', v.rprob η c' = 1 := by
  unfold rprob
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [← hv.2.1]
  refine sum_congr rfl fun c _ => ?_
  simp_rw [mul_assoc, ← mul_sum, ← sum_mul]
  rw [sum_regP _ (sig_nonneg hv c hη), sum_regP_center _ (by linarith [(hv.2.2.2.1 c).1]), one_mul,
    mul_one]

/-- Validity of a refined label. -/
lemma refine_OK (hp : p.Prime) {L : LData p} (hL : L.OK) (r : RData p L.G) {a t : ZMod p}
    {τ σ : ℝ} (hGood : (L.G.sub r.B).Good) (hm : ((2 * r.m : ℕ) : ZMod p) ≠ 0)
    (ha : snorm L.S (a - L.n) ≤ L.ρ / 2) (ht : snorm L.S t ≤ σ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hbud : L.ρ / 2 + σ + 2 * r.m * τ ≤ L.ρ) : (L.refine r a t τ).OK := by
  classical
  haveI := Fact.mk hp
  obtain ⟨⟨s, hs, hs0⟩, ⟨hρ0, hρ1⟩, hLip, hF1, hLQ, -⟩ := hL
  refine ⟨⟨s * ((2 * r.m : ℕ) : ZMod p)⁻¹, mem_image_of_mem _ (mem_insert_of_mem hs),
    mul_ne_zero hs0 (inv_ne_zero hm)⟩, ⟨hτ0, hτ1⟩, DTorus.isLip_sub hLip r.B _, fun x => hF1 _, ?_,
    hGood⟩
  change LocQuad (sBohr _ (a + t) τ) (fun x => r.π (L.Ξ x - L.Ξ (a + t)))
  refine ((hLQ.mono ?_).sub_const _).comp r.π
  intro x hx
  rw [mem_sBohr hτ0.le] at hx
  rw [mem_sBohr hρ0.le]
  have h1 : snorm L.S (x - (a + t)) ≤ (2 * r.m : ℕ) * τ := by
    refine (snorm_mono (subset_insert (r.ξ a) L.S) _).trans ?_
    refine (snorm_le_of_image_inv hp _ _ hm _).trans ?_
    exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
  have e : x - L.n = (a - L.n) + t + (x - (a + t)) := by abel
  rw [e]
  refine (snorm_add_le _ _).trans ?_
  have := snorm_add_le (S := L.S) (a - L.n) t
  push_cast at h1
  linarith

/-- Validity of the refined approximant. -/
theorem refined_valid (hp : p.Prime) (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hR : ∀ c, v.Poor η c → v.RProp η c (rd c)) (hN : ∀ c, v.Poor η c → v.NumOK η c (rd c)) :
    (v.refined η rd).Valid := by
  refine ofData_valid _ _ _ (rprob_nonneg hv) (sum_rprob hv hη) ?_
  rintro ⟨c, a, t⟩
  by_cases h : v.Ref η c a t
  · rw [rdata_pos h]
    obtain ⟨hpoor, ha, ht⟩ := h
    obtain ⟨hm1, -, -, hGood, -, -, -⟩ := hR c hpoor
    obtain ⟨hs0, hs8, hτ0, hτ1, -, h4m, -, -, -, hm⟩ := hN c hpoor
    have hρ0 := (hv.2.2.2.1 c).1
    refine refine_OK hp (ldata_OK hv c) (rd c) (σ := v.sig η c) hGood hm ?_ ?_ hτ0 hτ1 ?_
    · exact snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) ha) (by positivity)
    · exact snorm_le_of_mem (mem_bohr_of_regP_ne_zero hs0.le ht) hs0.le
    · change v.ρ c / 2 + v.sig η c + 2 * (rd c).m * v.tau η c ≤ v.ρ c
      nlinarith
  · rw [rdata_neg h]; exact ldata_OK hv c

/-! ### Statistics of the refined approximant -/

lemma sum_refined (rd : ∀ c, RData p (v.G c)) (Φ : LData p → ℝ) :
    ∑ c', v.rprob η c' * Φ (v.rdata η rd c') =
      ∑ c, v.prob c * ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
        ∑ t, regP (v.S c) (v.sig η c) t * Φ (v.rdata η rd (c, a, t)) := by
  unfold rprob
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => ?_
  simp_rw [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun t _ => ?_
  ring

lemma inner_nonpoor (hv : v.Valid) (hη : 0 < η) (rd : ∀ c, RData p (v.G c)) {c : v.C}
    (hc : ¬ v.Poor η c) (Φ : LData p → ℝ) :
    ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
      ∑ t, regP (v.S c) (v.sig η c) t * Φ (v.rdata η rd (c, a, t)) = Φ (v.ldata c) := by
  have e : ∀ a t, v.rdata η rd (c, a, t) = v.ldata c := fun a t => rdata_neg (fun h => hc h.1)
  simp_rw [e, ← sum_mul, sum_regP _ (sig_nonneg hv c hη), one_mul]
  rw [sum_regP_center _ (by linarith [(hv.2.2.2.1 c).1]), one_mul]

lemma inner_poor_le (rd : ∀ c, RData p (v.G c)) {c : v.C} (hc : v.Poor η c)
    (Φ : LData p → ℝ) (Ψ : ZMod p → ZMod p → ℝ)
    (hΦ : ∀ a t, v.Ref η c a t → Φ ((v.ldata c).refine (rd c) a t (v.tau η c)) ≤ Ψ a t) :
    ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
      ∑ t, regP (v.S c) (v.sig η c) t * Φ (v.rdata η rd (c, a, t)) ≤
    ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) * ∑ t, regP (v.S c) (v.sig η c) t * Ψ a t := by
  refine sum_le_sum fun a _ => ?_
  by_cases ha : regP (v.S c) (v.ρ c / 2) (a - v.n c) = 0
  · simp [ha]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => ?_) (regP_nonneg _ _)
  by_cases ht : regP (v.S c) (v.sig η c) t = 0
  · simp [ht]
  have hR : v.Ref η c a t := ⟨hc, ha, ht⟩
  rw [rdata_pos hR]
  exact mul_le_mul_of_nonneg_left (hΦ a t hR) (regP_nonneg _ _)

lemma avg_shift (L : LData p) (g : ZMod p → ℝ) :
    L.avg g = ∑ y, regP L.S (L.ρ / 2) y * g (L.n + y) := by
  unfold LData.avg
  exact (Fintype.sum_equiv (Equiv.addLeft L.n) _ _ fun y => by simp).symm

/-- The dilated frequency set of the label `(c, a, ·)`. -/
def rS (rd : ∀ c, RData p (v.G c)) (c : v.C) (a : ZMod p) : Finset (ZMod p) :=
  (insert ((rd c).ξ a) (v.S c)).image (fun s => s * ((2 * (rd c).m : ℕ) : ZMod p)⁻¹)

lemma snorm_le_of_rS (hp : p.Prime) (rd : ∀ c, RData p (v.G c)) {c : v.C}
    (hm : ((2 * (rd c).m : ℕ) : ZMod p) ≠ 0) (a y : ZMod p) :
    snorm (v.S c) y ≤ (2 * (rd c).m : ℕ) * snorm (v.rS rd c a) y :=
  (snorm_mono (subset_insert _ _) _).trans (snorm_le_of_image_inv hp _ _ hm _)

lemma p71L_nonneg {S : Finset (ZMod p)} {G : DTorus} {η ε4 ρ : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε4)
    (hρ : 0 ≤ ρ) (m : ℕ) : 0 ≤ p71L S G η ε4 ρ m := by
  unfold p71L p71E p71K p71R p71A lqK lqR lqτ p71δ wρh wδ wP
  positivity

/-- The pointwise approximation on a refined label. -/
lemma refine_err (hp : p.Prime) (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)} {c : v.C}
    (hR : v.RProp η c (rd c)) (hN : v.NumOK η c (rd c)) {a t : ZMod p} (hRef : v.Ref η c a t)
    {y : ZMod p} (hy : regP (v.rS rd c a) (v.tau η c / 2) y ≠ 0) :
    |v.F c (v.Ξ c (a + t + y)) - ((v.ldata c).refine (rd c) a t (v.tau η c)).F
      (((v.ldata c).refine (rd c) a t (v.tau η c)).Ξ (a + t + y))| ≤ η ^ C3 / 4 := by
  haveI := Fact.mk hp
  obtain ⟨hm1, -, -, -, -, -, herr⟩ := hR
  obtain ⟨hs0, hs8, hτ0, -, -, h4m, -, hnumL, -, hm⟩ := hN
  obtain ⟨-, ha, ht⟩ := hRef
  have hρ0 := (hv.2.2.2.1 c).1
  set m := (rd c).m with hmdef
  set k : ZMod p := ((2 * m : ℕ) : ZMod p) with hk
  obtain ⟨h, rfl⟩ : ∃ h, y = k * h := ⟨k⁻¹ * y, by rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]⟩
  have hσ : snorm (insert ((rd c).ξ a) (v.S c)) h ≤ v.tau η c / 2 := by
    have := snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) hy) (by positivity)
    unfold rS at this
    rwa [snorm_image_mul, ← mul_assoc, inv_mul_cancel₀ hm, one_mul] at this
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hτs : v.tau η c / 2 ≤ v.sig η c := by nlinarith
  have hA := snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) ha) (by positivity)
  have hT := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hs0.le ht) hs0.le
  have := herr a hA (a + t) h (by simpa using hT) (hσ.trans hτs) (by nlinarith)
  refine this.trans ?_
  have hL0 := p71L_nonneg (S := v.S c) (G := v.G c) (ε4 := eps4 η) hη.le
    (by unfold eps4; positivity) hρ0.le m
  refine le_trans ?_ hnumL
  gcongr

/-- **Energy**: the energy increases by at most `2 η^{C₃}`. -/
theorem energy_refined (hp : p.Prime) (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hR : ∀ c, v.Poor η c → v.RProp η c (rd c)) (hN : ∀ c, v.Poor η c → v.NumOK η c (rd c))
    (f : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ((v.refined η rd).triple η).energy f ≤ (v.triple η).energy f + 2 * η ^ C3 := by
  have heps : 0 ≤ eps4 η := (Real.exp_pos _).le
  have hv' := refined_valid hp hv hη hR hN
  have hC : (0 : ℝ) ≤ η ^ C3 := by positivity
  rw [energy_eq _ η heps (fun c' => (hv'.2.2.2.1 c').1.le),
    energy_eq v η heps (fun c => (hv.2.2.2.1 c).1.le)]
  set Φ : LData p → ℝ := fun L => L.avg (fun x => (f x - L.F (L.Ξ x)) ^ 2) with hΦ
  change ∑ c', v.rprob η c' * Φ (v.rdata η rd c') ≤ ∑ c, v.prob c * Φ (v.ldata c) + _
  rw [sum_refined _ Φ]
  have hsum : ∑ c, v.prob c * Φ (v.ldata c) + 2 * η ^ C3 =
      ∑ c, v.prob c * (Φ (v.ldata c) + 2 * η ^ C3) := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hv.2.1, one_mul]
  rw [hsum]
  refine sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (hv.1 c)
  by_cases hc : v.Poor η c
  · have hRc := hR c hc
    have hNc := hN c hc
    obtain ⟨hs0, hs8, hτ0, -, -, h4m, hnum, -, -, hm⟩ := hN c hc
    have hρ0 := (hv.2.2.2.1 c).1
    set g : ZMod p → ℝ := fun x => (f x - v.F c (v.Ξ c x)) ^ 2 with hg
    have hQ1 : ∀ a, ∑ y, regP (v.rS rd c a) (v.tau η c / 2) y = 1 :=
      fun a => sum_regP _ (by positivity)
    have h1 := inner_poor_le rd hc Φ
      (fun a t => ∑ y, regP (v.rS rd c a) (v.tau η c / 2) y * g (a + t + y) + η ^ C3)
      (fun a t hRef => by
        change LData.avg _ _ ≤ _
        rw [avg_shift]
        change ∑ y, regP (v.rS rd c a) (v.tau η c / 2) y * (f (a + t + y) -
          ((v.ldata c).refine (rd c) a t (v.tau η c)).F
            (((v.ldata c).refine (rd c) a t (v.tau η c)).Ξ (a + t + y))) ^ 2 ≤ _
        have e : ∑ y, regP (v.rS rd c a) (v.tau η c / 2) y * g (a + t + y) + η ^ C3 =
            ∑ y, regP (v.rS rd c a) (v.tau η c / 2) y * (g (a + t + y) + η ^ C3) := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hQ1, one_mul]
        beta_reduce
        rw [e]
        refine sum_le_sum fun y _ => ?_
        by_cases hy : regP (v.rS rd c a) (v.tau η c / 2) y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (regP_nonneg _ _)
        have herr := refine_err hp hv hη hRc hNc hRef hy
        set F1 := v.F c (v.Ξ c (a + t + y))
        set F2 := ((v.ldata c).refine (rd c) a t (v.tau η c)).F
            (((v.ldata c).refine (rd c) a t (v.tau η c)).Ξ (a + t + y))
        have hF1 : |F1| ≤ 1 := hv.2.2.2.2.2.1 c _
        have hF2 : |F2| ≤ 1 := hv.2.2.2.2.2.1 c _
        change (f (a + t + y) - F2) ^ 2 ≤ (f (a + t + y) - F1) ^ 2 + η ^ C3
        obtain ⟨hf0, hf1⟩ := hf (a + t + y)
        have e2 : (f (a + t + y) - F2) ^ 2 - (f (a + t + y) - F1) ^ 2 =
            (F1 - F2) * (2 * f (a + t + y) - F1 - F2) := by ring
        have h3 : |2 * f (a + t + y) - F1 - F2| ≤ 4 := by
          rw [abs_le] at hF1 hF2 ⊢; constructor <;> linarith
        have : (F1 - F2) * (2 * f (a + t + y) - F1 - F2) ≤ η ^ C3 / 4 * 4 := by
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          exact mul_le_mul herr h3 (abs_nonneg _) (by positivity)
        linarith)
    refine h1.trans ?_
    have e : ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) * ∑ t, regP (v.S c) (v.sig η c) t *
        (∑ y, regP (v.rS rd c a) (v.tau η c / 2) y * g (a + t + y) + η ^ C3) =
        ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) * ∑ t, regP (v.S c) (v.sig η c) t *
          ∑ y, regP (v.rS rd c a) (v.tau η c / 2) y * g (a + t + y) + η ^ C3 := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, sum_regP _ hs0.le, one_mul]
      rw [sum_regP_center _ (by positivity), one_mul]
    rw [e]
    have hg4 : ∀ x, |g x| ≤ 4 := by
      intro x
      have := hv.2.2.2.2.2.1 c (v.Ξ c x)
      obtain ⟨hf0, hf1⟩ := hf x
      rw [abs_le] at this
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith
    have hmix := tv_mix (S := v.S c) (n0 := v.n c) hρ0 hs0
      (mul_nonneg (Nat.cast_nonneg _) hτ0.le) h4m hs8
      (fun a y => regP (v.rS rd c a) (v.tau η c / 2) y) (fun a y => regP_nonneg _ _)
      hQ1 (fun a y hy => by
        have hyb := snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) hy)
          (by positivity)
        have := snorm_le_of_rS hp rd hm a y
        push_cast at this
        nlinarith [Nat.cast_nonneg (α := ℝ) (rd c).m]) g hg4
    rw [← mul_add] at hmix
    have h4 : 4 * (50 * (v.S c).card * ((rd c).m * v.tau η c) / v.sig η c +
        50 * (v.S c).card * v.sig η c / (v.ρ c / 2)) ≤ η ^ C3 := by linarith
    have hΦc : Φ (v.ldata c) = ∑ x, regP (v.S c) (v.ρ c / 2) (x - v.n c) * g x := rfl
    rw [hΦc]
    have := (abs_le.mp (hmix.trans h4)).2
    linarith
  · have hin := inner_nonpoor hv hη rd hc Φ
    rw [hin]
    linarith

/-! ### Structural statistics -/

end SLA

end

end GT
end File_GT_BadDim

open Finset KM Matrix
open GT GT.SLA in
theorem solution {p : ℕ} [NeZero p] {v : SLA p} {η : ℝ} (hp : p.Prime) (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hR : ∀ c, v.Poor η c → v.RProp η c (rd c)) (hN : ∀ c, v.Poor η c → v.NumOK η c (rd c))
    (f : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ((v.refined η rd).triple η).energy f ≤ (v.triple η).energy f + 2 * η ^ C3 :=
  @GT.SLA.energy_refined p _ v η hp hv hη rd hR hN f hf

