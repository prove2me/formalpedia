-- Prove2me | solution 1 for GT.u3_mid
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:49.073652+00:00
-- url     : https://prove2.me/submissions/287f07ad-64d1-4555-9cbd-c7f9de2af0c8

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_pordo
import Theorems.Thm_GT_u3_step4
import Theorems.Thm_GT_u3_step5

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

lemma sum_sub_right (f : G → ℝ) (t : G) : ∑ x, f (x - t) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.subRight t) _ _ (fun _ => rfl)

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

section File_KM_Fourier
/-!
# Fourier analysis on `ZMod N`
-/

open Finset
open ComplexConjugate

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma ech_add (a b : ZMod N) : ech (a + b) = ech a * ech b := AddChar.map_add_eq_mul _ _ _

/-- `|e(z) - 1| ≤ 2π ‖z/N‖`. -/
lemma norm_ech_sub_one_le (z : ZMod N) : ‖ech z - 1‖ ≤ 2 * Real.pi * cn z := by
  have h1 : ech z = Complex.exp (Complex.I * ((2 * Real.pi * sc z : ℝ) : ℂ)) := by
    unfold ech
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    unfold sc
    set u : ℝ := (z.val : ℝ) / N
    have : 2 * ↑Real.pi * Complex.I * ↑z.val / ↑N =
        Complex.I * ((2 * Real.pi * (u - round u) : ℝ) : ℂ) + (round u : ℤ) * (2 * Real.pi * Complex.I) := by
      simp only [u]; push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), cn_eq_abs_sc]

end

end KM
end File_KM_Fourier

section File_GT_Weyl
/-!
# A multidimensional Weyl lemma on the grid `(ZMod N)^κ`

Let `f : (κ → ZMod N) → ℝ` be bounded by `B`, have mean zero, and be Lipschitz in the sense
`|f y - f (y - h)| ≤ W ∑ᵢ ‖hᵢ/N‖`.  If a weighted average `∑ⱼ ωⱼ f(yⱼ)` (with `∑|ωⱼ| ≤ 1`) is
at least `δ` in absolute value, then some non-zero frequency `k` with `|kᵢ| < 2M` has
`2B(2M)^{|κ|} ‖∑ⱼ ωⱼ e(k·yⱼ/N)‖ ≥ δ`, as soon as `W|κ|/M < δ/2`.

The proof smooths `f` with the product Jackson kernel, which is a short non-negative
combination of characters.
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N]

lemma norm_ech (z : ZMod N) : ‖ech z‖ = 1 := by
  unfold ech; simp

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

end

end GT
end File_GT_Weyl

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

/-- Weighted Jensen: `(∑ pᵢ aᵢ)² ≤ ∑ pᵢ aᵢ²` for a probability vector `p`. -/
lemma sq_wavg_le {ι : Type*} [Fintype ι] {p : ι → ℝ} (a : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) : (∑ i, p i * a i) ^ 2 ≤ ∑ i, p i * a i ^ 2 := by
  have := sum_mul_sq_le_sq_mul_sq univ (fun i => √(p i)) (fun i => √(p i) * a i)
  have e1 : ∀ i, √(p i) * (√(p i) * a i) = p i * a i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hp i)]
  have e2 : ∀ i, √(p i) ^ 2 = p i := fun i => Real.sq_sqrt (hp i)
  have e3 : ∀ i, (√(p i) * a i) ^ 2 = p i * a i ^ 2 := fun i => by rw [mul_pow, e2]
  simp only [e1, e2, e3, hp1, one_mul] at this
  exact this

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

@[simp] lemma snorm_neg (h : ZMod N) : snorm S (-h) = snorm S h := by
  unfold snorm; simp [mul_neg, cn_neg]

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

lemma regP_isDist (Γ : Finset (ZMod N)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∀ x, 0 ≤ regP Γ ρ x) ∧ ∑ x, regP Γ ρ x = 1 :=
  ⟨fun x => regP_nonneg Γ x, sum_regP Γ hρ⟩

/-! ### Averages against probability vectors -/

section avg

variable {α : Type*} [Fintype α] {P : α → ℝ}

lemma norm_wavg_sub_le (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (F : α → ℂ) (c : ℂ) {δ : ℝ}
    (h : ∀ x, P x ≠ 0 → ‖F x - c‖ ≤ δ) : ‖∑ x, (P x : ℂ) * F x - c‖ ≤ δ := by
  have e : ∑ x, (P x : ℂ) * F x - c = ∑ x, (P x : ℂ) * (F x - c) := by
    rw [eq_comm]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, ← Complex.ofReal_sum, hP1]
    simp
  rw [e]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun x _ => ?_).trans (le_of_eq (by
    rw [← sum_mul, hP1, one_mul] : ∑ x, P x * δ = δ)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP x)]
  by_cases hx : P x = 0
  · rw [hx, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h x hx) (hP x)

lemma norm_wavg_le (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (F : α → ℂ) {B : ℝ}
    (h : ∀ x, P x ≠ 0 → ‖F x‖ ≤ B) : ‖∑ x, (P x : ℂ) * F x‖ ≤ B := by
  simpa using norm_wavg_sub_le hP hP1 F 0 (fun x hx => by simpa using h x hx)

lemma wavg_le (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (F : α → ℝ) {B : ℝ}
    (h : ∀ x, P x ≠ 0 → F x ≤ B) : ∑ x, P x * F x ≤ B := by
  calc ∑ x, P x * F x ≤ ∑ x, P x * B := sum_le_sum fun x _ => by
        by_cases hx : P x = 0
        · rw [hx, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h x hx) (hP x)
    _ = B := by rw [← sum_mul, hP1, one_mul]

end avg

end

end GT
end File_GT_Prob

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

end

end GT
end File_GT_MixTV

section File_GT_U3Util
/-!
# Utilities for the local inverse `U³` theorem

Cauchy–Schwarz eliminations, the real `8`-point box average, popularity, and translation of
regular variables.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

section cs

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

end cs

variable {p : ℕ} [NeZero p]

/-! ### Translating regular variables -/

/-- Translation by an element of small `S^⊥`-norm, real version with a norm hypothesis. -/
lemma shift_real {Γ Γ' : Finset (ZMod p)} (hΓ : Γ ⊆ Γ') {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (h4 : 4 * ρ' ≤ ρ) {h : ZMod p} (hh : snorm Γ' h ≤ ρ') {B : ℝ}
    (g : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ B) :
    |∑ x, regP Γ ρ x * g (x + h) - ∑ x, regP Γ ρ x * g x| ≤ B * (50 * Γ.card * ρ' / ρ) := by
  have hρ' : 0 ≤ ρ' := (snorm_nonneg h).trans hh
  exact regP_shift_real hΓ hρ hρ' h4 ((mem_bohr_iff_snorm hρ').2 hh) g hg

/-- Translation of a centred regular variable. -/
lemma shift_real_c {Γ Γ' : Finset (ZMod p)} (hΓ : Γ ⊆ Γ') {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (h4 : 4 * ρ' ≤ ρ) {h : ZMod p} (hh : snorm Γ' h ≤ ρ') (n0 : ZMod p) {B : ℝ}
    (g : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ B) :
    |∑ x, regP Γ ρ (x - n0) * g (x + h) - ∑ x, regP Γ ρ (x - n0) * g x| ≤
      B * (50 * Γ.card * ρ' / ρ) := by
  have e : ∀ G : ZMod p → ℝ, ∑ x, regP Γ ρ (x - n0) * G x = ∑ x, regP Γ ρ x * G (x + n0) := by
    intro G
    exact (Fintype.sum_equiv (Equiv.addRight n0) _ _ (fun x => by simp)).symm
  rw [e, e]
  have := shift_real hΓ hρ h4 hh (fun x => g (x + n0)) (fun x => hg _)
  simp only [add_right_comm _ h n0] at this ⊢
  exact this

/-- Two simultaneous translations of a pair of independent regular variables. -/
lemma shift_pair {Γ : Finset (ZMod p)} {ρ ρr σ σr : ℝ} (hρ : 0 < ρ) (hρr : 0 < ρr)
    (h4 : 4 * σ ≤ ρ) (h4r : 4 * σr ≤ ρr) {s t : ZMod p} (hs : snorm Γ s ≤ σ)
    (ht : snorm Γ t ≤ σr) (n0 : ZMod p) (Φ : ZMod p → ZMod p → ℝ) (hΦ : ∀ a r, |Φ a r| ≤ 1) :
    |∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) (r + t) -
      ∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ a r| ≤
      50 * Γ.card * σ / ρ + 50 * Γ.card * σr / ρr := by
  have hσr : 0 ≤ σr := (snorm_nonneg t).trans ht
  have hσ : 0 ≤ σ := (snorm_nonneg s).trans hs
  -- first shift `r`
  have e1 : ∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) (r + t) -
      ∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) r =
      ∑ a, regP Γ ρ (a - n0) * (∑ r, regP Γ ρr r * Φ (a + s) (r + t) -
        ∑ r, regP Γ ρr r * Φ (a + s) r) := by
    rw [← sum_sub_distrib]; refine sum_congr rfl fun a _ => ?_
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by ring
  have b1 : |∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) (r + t) -
      ∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) r| ≤
      50 * Γ.card * σr / ρr := by
    rw [e1]
    have hP := regP_isDist Γ (ρ := ρ) (by linarith)
    have hPc : ∀ a, 0 ≤ regP Γ ρ (a - n0) := fun a => regP_nonneg _ _
    have hPc1 : ∑ a, regP Γ ρ (a - n0) = 1 := by
      rw [sum_sub_right (regP Γ ρ) n0]; exact hP.2
    refine abs_wavg_le hPc hPc1 _ (fun a _ => ?_)
    have := shift_real subset_rfl hρr h4r ht (fun r => Φ (a + s) r) (fun r => hΦ _ _)
    simpa using this
  -- then shift `a`
  have e2 : ∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) r -
      ∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ a r =
      ∑ a, regP Γ ρ (a - n0) * (∑ r, regP Γ ρr r * Φ (a + s) r) -
        ∑ a, regP Γ ρ (a - n0) * (∑ r, regP Γ ρr r * Φ a r) := by
    congr 1 <;> refine sum_congr rfl fun a _ => ?_ <;> rw [mul_sum] <;>
      exact sum_congr rfl fun r _ => by ring
  have b2 : |∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) r -
      ∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ a r| ≤ 50 * Γ.card * σ / ρ := by
    rw [e2]
    have hQ := regP_isDist Γ (ρ := ρr) hρr.le
    have := shift_real_c subset_rfl hρ h4 hs n0 (fun a => ∑ r, regP Γ ρr r * Φ a r)
      (B := 1) (fun a => abs_wavg_le hQ.1 hQ.2 _ (fun r _ => hΦ _ _))
    simpa using this
  have := abs_sub_le (∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) (r + t))
    (∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ (a + s) r)
    (∑ a, ∑ r, regP Γ ρ (a - n0) * regP Γ ρr r * Φ a r)
  linarith

end

end GT
end File_GT_U3Util

section File_GT_U3Base
/-!
# Basic tools for the local inverse `U³` theorem

* symmetry of regular distributions;
* `Good T A l`: the character `x ↦ e(l x / p)` is `A`-Lipschitz with respect to `‖·‖_{T^⊥}`
  (a substitute for the word norm of Green–Tao);
* large exponential sums over regular Bohr distributions force goodness;
* a box Cauchy–Schwarz inequality with a general bounded kernel;
* translation estimates for centred regular variables.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Symmetry -/

lemma sum_regP_center' (Γ : Finset (ZMod p)) {ρ : ℝ} (hρ : 0 ≤ ρ) (c : ZMod p) :
    ∑ x, regP Γ ρ (x - c) = 1 := by
  rw [sum_sub_right (regP Γ ρ) c]; exact sum_regP Γ hρ

lemma regP_center_isDist (Γ : Finset (ZMod p)) {ρ : ℝ} (hρ : 0 ≤ ρ) (c : ZMod p) :
    (∀ x, 0 ≤ regP Γ ρ (x - c)) ∧ ∑ x, regP Γ ρ (x - c) = 1 :=
  ⟨fun x => regP_nonneg _ _, sum_regP_center' Γ hρ c⟩

/-! ### Goodness -/

namespace Good

variable {T : Finset (ZMod p)} {A A' : ℝ} {l l' : ZMod p}

lemma neg (h : Good T A l) : Good T A (-l) := fun x => by rw [neg_mul, cn_neg]; exact h x

lemma add (h : Good T A l) (h' : Good T A' l') : Good T (A + A') (l + l') := fun x => by
  rw [add_mul, add_mul]; exact (cn_add_le _ _).trans (add_le_add (h x) (h' x))

lemma sub (h : Good T A l) (h' : Good T A' l') : Good T (A + A') (l - l') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

lemma mono_set {T' : Finset (ZMod p)} (h : Good T A l) (hT : T ⊆ T') (hA : 0 ≤ A) :
    Good T' A l := fun x => (h x).trans (mul_le_mul_of_nonneg_left (snorm_mono hT x) hA)

lemma iff_neg : Good T A (-l) ↔ Good T A l :=
  ⟨fun h => by simpa using h.neg, fun h => h.neg⟩

end Good

/-! ### Box Cauchy–Schwarz -/

section box

variable {α β : Type*} [Fintype α] [Fintype β]

lemma norm_wsum_sq_le {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (u : α → ℂ) :
    ‖∑ x, (P x : ℂ) * u x‖ ^ 2 ≤ ∑ x, P x * ‖u x‖ ^ 2 := by
  have h1 : ‖∑ x, (P x : ℂ) * u x‖ ≤ ∑ x, P x * ‖u x‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun x _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP x)]
  have h2 := sq_wavg_le (fun x => ‖u x‖) hP hP1
  calc ‖∑ x, (P x : ℂ) * u x‖ ^ 2 ≤ (∑ x, P x * ‖u x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end box

/-! ### Translations of centred regular variables -/

lemma shift_cplx_c {Γ Γ' : Finset (ZMod p)} (hΓ : Γ ⊆ Γ') {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (h4 : 4 * ρ' ≤ ρ) {h : ZMod p} (hh : snorm Γ' h ≤ ρ') (c : ZMod p) {B : ℝ}
    (G : ZMod p → ℂ) (hG : ∀ x, ‖G x‖ ≤ B) :
    ‖∑ x, (regP Γ ρ (x - c) : ℂ) * G (x + h) - ∑ x, (regP Γ ρ (x - c) : ℂ) * G x‖ ≤
      B * (50 * Γ.card * ρ' / ρ) := by
  have hρ' : 0 ≤ ρ' := (snorm_nonneg h).trans hh
  have e : ∀ F : ZMod p → ℂ, ∑ x, (regP Γ ρ (x - c) : ℂ) * F x =
      ∑ x, (regP Γ ρ x : ℂ) * F (x + c) := fun F =>
    (Fintype.sum_equiv (Equiv.addRight c) _ _ (fun x => by simp)).symm
  rw [e, e]
  have := regP_shift hΓ hρ hρ' h4 ((mem_bohr_iff_snorm hρ').2 hh) (fun x => G (x + c))
    (fun x => hG _)
  simp only [add_right_comm _ h c] at this ⊢
  exact this

end

end GT
end File_GT_U3Base

section File_GT_U3S3
/-!
# Local inverse `U³`, third step: random filters

(Green–Tao, Theorem 9.4.)  Random linear filters `Ξ(n) = λ n + ξ(n) h` keep additive quadruples
respected by `ξ` with probability `≈ 10⁻⁶` each, and very bad quadruples with probability at
most about half of that.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Doubling -/

/-! ### One filter -/

lemma le_wavg' {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (F : α → ℝ) {c : ℝ} (h : ∀ x, P x ≠ 0 → c ≤ F x) : c ≤ ∑ x, P x * F x := by
  have := wavg_le hP hP1 (fun x => -F x) (B := -c) (fun x hx => by linarith [h x hx])
  simp only [mul_neg, sum_neg_distrib] at this
  linarith

/-! ### Non-generic quadruples are rare -/

/-! ### Many filters -/

end

end GT
end File_GT_U3S3

section File_GT_U3S4c
/-!
# Local inverse `U³`, fourth step: neighbourhoods, energies and the score

Definitions for the score maximisation argument of Green–Tao, Theorem 9.5, and the
stability of the weighted average `QW` under the random refinement.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Scales -/

section scales

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRθ : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
include hR0 hRθ hθ0 hθ1

lemma R_lt_le {m n : ℕ} (h : m < n) : R n ≤ θ * R m := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · calc R (n + 1) ≤ θ * R n := hRθ n
        _ ≤ 1 * R n := mul_le_mul_of_nonneg_right hθ1 (hR0 n).le
        _ = R n := one_mul _
        _ ≤ θ * R m := ih h'
    · rw [← h']; exact hRθ m

lemma R_anti {m n : ℕ} (h : m ≤ n) : R n ≤ R m := by
  rcases h.lt_or_eq with h' | rfl
  · exact (R_lt_le hR0 hRθ hθ0 hθ1 h').trans (by nlinarith [hR0 m])
  · exact le_rfl

end scales

/-! ### Neighbourhoods -/

lemma ind_nonneg (A : Finset (ZMod p)) (u : ZMod p) : 0 ≤ ind A u := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (A : Finset (ZMod p)) (u : ZMod p) : ind A u ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-! ### Stability of `QW` under the random refinement -/

section stab

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16)
include hR0 hRk hθ0 hθ1

end stab

end

end GT
end File_GT_U3S4c

section File_GT_U3S4d
/-!
# Local inverse `U³`, fourth step: the energies under the random refinement

Pythagoras' theorem for the variances `E_i`, and the estimate (estable) of Green–Tao,
Theorem 9.5: under the random refinement no energy increases (up to a negligible error), and
the energy of the component with a large local `U²` norm decreases.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma alph_nonneg (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) : 0 ≤ alph R A T c j i :=
  sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _) (ind_nonneg _ _)

lemma alph_le_one {R : ℕ → ℝ} (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) (hR : 0 ≤ R (j + lvl i)) : alph R A T c j i ≤ 1 := by
  unfold alph
  calc ∑ u, regP T (R (j + lvl i)) (u - cent c i) * ind (A i) u
      ≤ ∑ u, regP T (R (j + lvl i)) (u - cent c i) * 1 :=
        sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (ind_le_one _ _) (regP_nonneg _ _)
    _ = 1 := by simp only [mul_one]; exact sum_regP_center' T hR _

section refine

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16)
include hR0 hRk hθ0 hθ1

end refine

end

end GT
end File_GT_U3S4d

section File_GT_U3S5a
/-!
# Local inverse `U³`: the weak mixing lemma (Green–Tao, Lemma 9.6)

If a bounded function `f` has a small local `U²` norm around a random point `n` of a Bohr
neighbourhood, then its convolution with any bounded function at a smaller scale is small in
mean square (estimate (po)), and dually (estimate (op)).
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma wavg_add_const {α : Type*} [Fintype α] {P : α → ℝ} (hP1 : ∑ x, P x = 1) (A : α → ℝ)
    (b : ℝ) : ∑ x, P x * (A x + b) = ∑ x, P x * A x + b := by
  simp only [mul_add, sum_add_distrib, ← sum_mul, hP1, one_mul]

section conc

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

end conc

end

end GT
end File_GT_U3S5a

section File_GT_U3S5b
/-!
# Local inverse `U³`, fifth step: a frequency function `ξ'` on a Bohr neighbourhood

Green–Tao, Theorem 9.7.  From the pseudorandom neighbourhood of the fourth step we build
`ξ'(a) = ξ(a₃(a)) + ξ(a - a₃(a))` for all `a` outside a small exceptional set, such that
`ξ'(a) ≈ ξ(a - a₂) + ξ(a₂)` for all but a small proportion (relative to `α₁α₂`) of the
decompositions `a = (a - a₂) + a₂` with `a - a₂ ∈ A₁`, `a₂ ∈ A₂`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Elementary probability -/

section prob

variable {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
include hP

include hP1

end prob

/-! ### The data of the fifth step -/

lemma I12_nonneg (A : Fin 4 → Finset (ZMod p)) (a a2 : ZMod p) : 0 ≤ I12 A a a2 :=
  mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _)

end

end GT
end File_GT_U3S5b

section File_GT_U3S6b
/-!
# Local inverse `U³`, Proposition 9.8: averaging tools
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma wswap {α β : Type*} [Fintype α] [Fintype β] (P : α → ℝ) (Q : β → ℝ) (F : α → β → ℝ) :
    ∑ a, P a * ∑ x, Q x * F a x = ∑ x, Q x * ∑ a, P a * F a x := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

section pen

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

end pen

end

end GT
end File_GT_U3S6b

section File_GT_U3S7a
/-!
# Local inverse `U³`, sixth step (Green–Tao, Theorem 9.9): majority vote
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma exists_le_wsum {α : Type*} [Fintype α] [Nonempty α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (F : α → ℝ) : ∃ x, F x ≤ ∑ y, P y * F y := by
  by_contra h
  push_neg at h
  have : ∑ y, P y * (∑ z, P z * F z) < ∑ y, P y * F y := by
    obtain ⟨y0, hy0⟩ : ∃ y, P y ≠ 0 := by
      by_contra h'; push_neg at h'; simp [h'] at hP1
    refine sum_lt_sum (fun y _ => mul_le_mul_of_nonneg_left (h y).le (hP y)) ⟨y0, mem_univ _, ?_⟩
    exact mul_lt_mul_of_pos_left (h y0) (lt_of_le_of_ne (hP y0) (Ne.symm hy0))
  rw [← sum_mul, hP1, one_mul] at this
  exact lt_irrefl _ this

lemma wswap3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (P : α → ℝ) (Q : β → ℝ)
    (Rw : γ → ℝ) (F : α → β → γ → ℝ) :
    ∑ h, P h * ∑ a, Q a * ∑ b, Rw b * F h a b = ∑ b, Rw b * ∑ h, P h * ∑ a, Q a * F h a b := by
  have e1 : ∀ h, ∑ a, Q a * ∑ b, Rw b * F h a b = ∑ b, Rw b * ∑ a, Q a * F h a b :=
    fun h => wswap _ _ _
  simp_rw [e1]
  exact wswap _ _ _

open Classical in
/-- Six good-or-bad indicators: if two decompositions are good then so is their difference. -/
lemma ind_good_sub_le {S : Finset (ZMod p)} {A A' : ℝ} (l l' : ZMod p) :
    (if Good S (A + A') (l - l') then (0 : ℝ) else 1) ≤
      (if Good S A l then 0 else 1) + (if Good S A' l' then 0 else 1) := by
  by_cases h1 : Good S A l
  · by_cases h2 : Good S A' l'
    · rw [if_pos (h1.sub h2), if_pos h1, if_pos h2]; norm_num
    · rw [if_neg h2]; split_ifs <;> norm_num
  · rw [if_neg h1]; split_ifs <;> norm_num

section majority

variable {T S : Finset (ZMod p)} {ρA ρH : ℝ} (hρA : 0 < ρA) (hρH : 0 < ρH) (a0 : ZMod p)
  (ξ' : ZMod p → ZMod p) (B : ℝ)
include hρA hρH

omit hρH in
open Classical in
/-- Pigeonholing the fourth element of the additive quadruple. -/
lemma exists_b0 {ep : ℝ}
    (hE : ∑ h, regP T ρH h * ∑ a, regP T ρA (a - a0) * ∑ b, regP T ρA (b - a0) *
      (if Good S (4 * B) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h)) then 0 else 1) ≤ ep) :
    ∃ b0, ∑ a, regP T ρA (a - a0) * ∑ h, regP T ρH h *
      (if Good S (4 * B) (ξ' a - ξ' (a + h) - ξ' b0 + ξ' (b0 + h)) then 0 else 1) ≤ ep := by
  have hPa := regP_center_isDist T hρA.le a0
  rw [wswap3] at hE
  obtain ⟨b0, hb0⟩ := exists_le_wsum hPa.1 hPa.2 (fun b => ∑ h, regP T ρH h *
    ∑ a, regP T ρA (a - a0) * (if Good S (4 * B) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h))
      then 0 else 1))
  refine ⟨b0, ?_⟩
  rw [wswap]
  exact hb0.trans hE

open Classical in
/-- Comparing `(a, h)` with `(a - n, h + n)`. -/
lemma exists_hn {ep r : ℝ} (hr4A : 4 * r ≤ ρA) (hr4H : 4 * r ≤ ρH) (b0 : ZMod p)
    (hb0 : ∑ a, regP T ρA (a - a0) * ∑ h, regP T ρH h *
      (if Good S (4 * B) (ξ' a - ξ' (a + h) - ξ' b0 + ξ' (b0 + h)) then 0 else 1) ≤ ep)
    (n : ZMod p) (hn : snorm T n ≤ r) :
    ∃ hn' : ZMod p, ∑ a, regP T ρA (a - a0) *
      (if Good S (8 * B) (ξ' a - ξ' (a - n) + ξ' (b0 + hn') - ξ' (b0 + hn' + n)) then 0 else 1) ≤
      2 * ep + (50 * T.card * r / ρA + 50 * T.card * r / ρH) := by
  have hPa := regP_center_isDist T hρA.le a0
  have hPh := regP_isDist T hρH.le
  set Φ : ZMod p → ZMod p → ℝ := fun a h =>
    if Good S (4 * B) (ξ' a - ξ' (a + h) - ξ' b0 + ξ' (b0 + h)) then 0 else 1 with hΦ
  have hΦ1 : ∀ a h, |Φ a h| ≤ 1 := fun a h => by
    simp only [hΦ]; split_ifs <;> norm_num
  have hsp := shift_pair hρA hρH hr4A hr4H (s := -n) (t := n) (by rw [snorm_neg]; exact hn) hn a0
    Φ hΦ1
  have eform : ∀ G : ZMod p → ZMod p → ℝ, ∑ a, ∑ h, regP T ρA (a - a0) * regP T ρH h * G a h =
      ∑ a, regP T ρA (a - a0) * ∑ h, regP T ρH h * G a h := fun G => by
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [eform, eform] at hsp
  have hsh : ∑ a, regP T ρA (a - a0) * ∑ h, regP T ρH h * Φ (a + -n) (h + n) ≤
      ep + (50 * T.card * r / ρA + 50 * T.card * r / ρH) := by
    have := (abs_le.1 hsp).2; linarith
  -- pointwise
  have hpt : ∀ a h, (if Good S (8 * B) (ξ' a - ξ' (a - n) + ξ' (b0 + h) - ξ' (b0 + h + n))
      then (0 : ℝ) else 1) ≤ Φ a h + Φ (a + -n) (h + n) := by
    intro a h
    have := ind_good_sub_le (S := S) (A := 4 * B) (A' := 4 * B)
      (ξ' a - ξ' (a + h) - ξ' b0 + ξ' (b0 + h))
      (ξ' (a + -n) - ξ' (a + -n + (h + n)) - ξ' b0 + ξ' (b0 + (h + n)))
    have e1 : a + -n + (h + n) = a + h := by ring
    have e2 : ξ' a - ξ' (a + h) - ξ' b0 + ξ' (b0 + h) -
        (ξ' (a + -n) - ξ' (a + -n + (h + n)) - ξ' b0 + ξ' (b0 + (h + n))) =
        ξ' a - ξ' (a - n) + ξ' (b0 + h) - ξ' (b0 + h + n) := by
      rw [e1, show a + -n = a - n by ring, show b0 + (h + n) = b0 + h + n by ring]; ring
    rw [e2, show 4 * B + 4 * B = 8 * B by ring] at this
    exact this
  have htot : ∑ a, regP T ρA (a - a0) * ∑ h, regP T ρH h *
      (if Good S (8 * B) (ξ' a - ξ' (a - n) + ξ' (b0 + h) - ξ' (b0 + h + n)) then 0 else 1) ≤
      2 * ep + (50 * T.card * r / ρA + 50 * T.card * r / ρH) := by
    calc _ ≤ ∑ a, regP T ρA (a - a0) * ∑ h, regP T ρH h * (Φ a h + Φ (a + -n) (h + n)) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (sum_le_sum fun h _ =>
            mul_le_mul_of_nonneg_left (hpt a h) (regP_nonneg _ _)) (regP_nonneg _ _)
      _ = ∑ a, regP T ρA (a - a0) * ∑ h, regP T ρH h * Φ a h +
          ∑ a, regP T ρA (a - a0) * ∑ h, regP T ρH h * Φ (a + -n) (h + n) := by
          simp only [mul_add, sum_add_distrib]
      _ ≤ _ := by linarith
  rw [wswap] at htot
  obtain ⟨h0, hh0⟩ := exists_le_wsum hPh.1 hPh.2 (fun h => ∑ a, regP T ρA (a - a0) *
    (if Good S (8 * B) (ξ' a - ξ' (a - n) + ξ' (b0 + h) - ξ' (b0 + h + n)) then 0 else 1))
  exact ⟨h0, hh0.trans htot⟩

open Classical in
/-- **Theorem 9.9** (sixth step): majority vote. -/
theorem majority {ep r : ℝ} (hr4A : 4 * r ≤ ρA) (hr4H : 4 * r ≤ ρH)
    (hE : ∑ h, regP T ρH h * ∑ a, regP T ρA (a - a0) * ∑ b, regP T ρA (b - a0) *
      (if Good S (4 * B) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h)) then 0 else 1) ≤ ep)
    (hsmall : 3 * (2 * ep + (50 * T.card * r / ρA + 50 * T.card * r / ρH)) +
      50 * T.card * (r / 2) / ρA < 1) :
    ∃ ξ'' : ZMod p → ZMod p,
      (∀ n, snorm T n ≤ r → ∑ a, regP T ρA (a - a0) *
        (if Good S (8 * B) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1) ≤
          2 * ep + (50 * T.card * r / ρA + 50 * T.card * r / ρH)) ∧
      ∀ n m, snorm T n ≤ r / 2 → snorm T m ≤ r / 2 →
        Good S (24 * B) (ξ'' (n + m) - ξ'' n - ξ'' m) := by
  set e6 := 2 * ep + (50 * T.card * r / ρA + 50 * T.card * r / ρH) with he6
  have hPa := regP_center_isDist T hρA.le a0
  obtain ⟨b0, hb0⟩ := exists_b0 hρA a0 ξ' B hE
  have hex : ∀ n, ∃ h' : ZMod p, snorm T n ≤ r → ∑ a, regP T ρA (a - a0) *
      (if Good S (8 * B) (ξ' a - ξ' (a - n) + ξ' (b0 + h') - ξ' (b0 + h' + n)) then 0 else 1) ≤
        e6 := by
    intro n
    by_cases hn : snorm T n ≤ r
    · obtain ⟨h', hh'⟩ := exists_hn hρA hρH a0 ξ' B hr4A hr4H b0 hb0 n hn
      exact ⟨h', fun _ => hh'⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose hf hhf using hex
  refine ⟨fun n => ξ' (b0 + hf n + n) - ξ' (b0 + hf n), ?_, ?_⟩
  · intro n hn
    have e : ∀ a, ξ' a - ξ' (a - n) - (ξ' (b0 + hf n + n) - ξ' (b0 + hf n)) =
        ξ' a - ξ' (a - n) + ξ' (b0 + hf n) - ξ' (b0 + hf n + n) := fun a => by ring
    simp_rw [e]
    exact hhf n hn
  · intro n m hn hm
    set ξ'' : ZMod p → ZMod p := fun n => ξ' (b0 + hf n + n) - ξ' (b0 + hf n) with hξ''
    have sen : ∀ n, snorm T n ≤ r → ∑ a, regP T ρA (a - a0) *
        (if Good S (8 * B) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1) ≤ e6 := by
      intro n hn
      have e : ∀ a, ξ' a - ξ' (a - n) - ξ'' n =
          ξ' a - ξ' (a - n) + ξ' (b0 + hf n) - ξ' (b0 + hf n + n) := fun a => by
        simp only [hξ'']; ring
      simp_rw [e]
      exact hhf n hn
    have hr0 : 0 ≤ r := by linarith [snorm_nonneg (S := T) n]
    have s1 := sen n (by linarith)
    have s2 := sen (n + m) ((snorm_add_le n m).trans (by linarith))
    have s3 := sen m (by linarith)
    have s3' := shift_real_c subset_rfl hρA (show 4 * (r / 2) ≤ ρA by linarith)
      (h := -n) (by rw [snorm_neg]; exact hn) a0 (B := (1 : ℝ))
      (fun a => if Good S (8 * B) (ξ' a - ξ' (a - m) - ξ'' m) then (0 : ℝ) else 1)
      (fun a => by (try dsimp only); split_ifs <;> norm_num)
    simp only [one_mul] at s3'
    have s3'' := (abs_le.1 s3').2
    by_contra hbad
    have hpt : ∀ a, (1 : ℝ) ≤
        (if Good S (8 * B) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1) +
        (if Good S (8 * B) (ξ' a - ξ' (a - (n + m)) - ξ'' (n + m)) then 0 else 1) +
        (if Good S (8 * B) (ξ' (a + -n) - ξ' (a + -n - m) - ξ'' m) then 0 else 1) := by
      intro a
      by_cases g1 : Good S (8 * B) (ξ' a - ξ' (a - n) - ξ'' n)
      · by_cases g2 : Good S (8 * B) (ξ' a - ξ' (a - (n + m)) - ξ'' (n + m))
        · by_cases g3 : Good S (8 * B) (ξ' (a + -n) - ξ' (a + -n - m) - ξ'' m)
          · exfalso; apply hbad
            have := ((g2.sub g1).sub g3).neg
            have e : -(ξ' a - ξ' (a - (n + m)) - ξ'' (n + m) - (ξ' a - ξ' (a - n) - ξ'' n) -
                (ξ' (a + -n) - ξ' (a + -n - m) - ξ'' m)) = ξ'' (n + m) - ξ'' n - ξ'' m := by
              rw [show a + -n = a - n by ring, show a - n - m = a - (n + m) by ring]; ring
            rw [e, show 8 * B + 8 * B + 8 * B = 24 * B by ring] at this
            exact this
          · rw [if_neg g3, if_pos g1, if_pos g2]; norm_num
        · rw [if_neg g2]; split_ifs <;> norm_num
      · rw [if_neg g1]; split_ifs <;> norm_num
    have hsum := sum_le_sum fun a (_ : a ∈ univ) => mul_le_mul_of_nonneg_left (hpt a) (hPa.1 a)
    rw [← sum_mul, hPa.2, one_mul] at hsum
    simp only [mul_add, sum_add_distrib] at hsum
    linarith

end majority

end

end GT
end File_GT_U3S7a

section File_GT_U3S7b
/-!
# Local inverse `U³`, Proposition 9.10 (combinatorial part)

From the fifth and sixth steps we find a shift `a₀` and a frequency `ξ₀` such that, for many `n`
in a small Bohr set, `a₀ - n ∈ A₁` and `ξ''(n) + ξ(a₀ - n) - ξ₀` is good.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma exists_ge_wsum {α : Type*} [Fintype α] [Nonempty α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (F : α → ℝ) : ∃ x, ∑ y, P y * F y ≤ F x := by
  obtain ⟨x, hx⟩ := exists_le_wsum hP hP1 (fun y => -F y)
  refine ⟨x, ?_⟩
  simp only [mul_neg, sum_neg_distrib] at hx
  linarith

section dfA

variable {R : ℕ → ℝ} {T S : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} (hR0 : ∀ t, 0 < R t)
include hR0

open Classical in
/-- Pointwise estimate behind Proposition 9.10. -/
lemma dfA_pt (ρv : ℝ) (ξ ξ' ξ'' : ZMod p → ZMod p) (Gd : Finset (ZMod p)) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hGd2 : ∀ a ∈ Gd, |g12 R A T c j a - alph R A T c j 0 * alph R A T c j 1| ≤
        alph R A T c j 0 * alph R A T c j 1 / 10 ∧
      ∑ x, regP T (R (j + 2)) x * (I12 A a (cent c 1 + x) *
        vb S ρv (ξ' a - ξ (a - (cent c 1 + x)) - ξ (cent c 1 + x))) ≤
        2 * t * (alph R A T c j 0 * alph R A T c j 1)) (a n : ZMod p) :
    (9 / 10 - 2 * t) * (alph R A T c j 0 * alph R A T c j 1) * ((if a - n ∈ Gd then 1 else 0) -
      (if Good S (8 * (1 / ρv)) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1)) ≤
      ∑ x, regP T (R (j + 2)) x * (I12 A (a - n) (cent c 1 + x) *
        (if Good S (9 * (1 / ρv))
          (ξ' a - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x) - ξ'' n) then 1 else 0)) := by
  set α0 := alph R A T c j 0
  set α1 := alph R A T c j 1
  have hα0 : 0 ≤ α0 := alph_nonneg R A T c j 0
  have hα1 : 0 ≤ α1 := alph_nonneg R A T c j 1
  have hα0' : α0 ≤ 1 := alph_le_one A T c j 0 (hR0 _).le
  have hα1' : α1 ≤ 1 := alph_le_one A T c j 1 (hR0 _).le
  have hαα : α0 * α1 ≤ 1 := mul_le_one₀ hα0' hα1 hα1'
  have hRHS0 : 0 ≤ ∑ x, regP T (R (j + 2)) x * (I12 A (a - n) (cent c 1 + x) *
      (if Good S (9 * (1 / ρv))
        (ξ' a - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x) - ξ'' n) then (1 : ℝ) else 0)) :=
    sum_nonneg fun x _ => mul_nonneg (regP_nonneg _ _) (mul_nonneg (I12_nonneg _ _ _)
      (by split_ifs <;> norm_num))
  by_cases hs : Good S (8 * (1 / ρv)) (ξ' a - ξ' (a - n) - ξ'' n)
  · rw [if_pos hs, sub_zero]
    -- the good decompositions of `a - n`
    have hpt : ∀ x, I12 A (a - n) (cent c 1 + x) *
        (1 - vb S ρv (ξ' (a - n) - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x))) ≤
        I12 A (a - n) (cent c 1 + x) * (if Good S (9 * (1 / ρv))
          (ξ' a - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x) - ξ'' n) then 1 else 0) := by
      intro x
      refine mul_le_mul_of_nonneg_left ?_ (I12_nonneg _ _ _)
      unfold vb
      by_cases hg : Good S (1 / ρv) (ξ' (a - n) - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x))
      · have := hs.add hg
        rw [show 8 * (1 / ρv) + 1 / ρv = 9 * (1 / ρv) by ring,
          show ξ' a - ξ' (a - n) - ξ'' n + (ξ' (a - n) - ξ (a - n - (cent c 1 + x)) -
            ξ (cent c 1 + x)) = ξ' a - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x) - ξ'' n
            by ring] at this
        rw [if_pos hg, if_pos this]; norm_num
      · rw [if_neg hg]; split_ifs <;> norm_num
    have hsum : g12 R A T c j (a - n) - ∑ x, regP T (R (j + 2)) x *
        (I12 A (a - n) (cent c 1 + x) * vb S ρv (ξ' (a - n) -
          ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x))) ≤
        ∑ x, regP T (R (j + 2)) x * (I12 A (a - n) (cent c 1 + x) *
          (if Good S (9 * (1 / ρv))
            (ξ' a - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x) - ξ'' n) then 1 else 0)) := by
      unfold g12
      rw [← sum_sub_distrib]
      refine sum_le_sum fun x _ => ?_
      rw [← mul_sub, show I12 A (a - n) (cent c 1 + x) - I12 A (a - n) (cent c 1 + x) *
        vb S ρv (ξ' (a - n) - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x)) =
        I12 A (a - n) (cent c 1 + x) * (1 - vb S ρv (ξ' (a - n) -
          ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x))) by ring]
      exact mul_le_mul_of_nonneg_left (hpt x) (regP_nonneg _ _)
    by_cases hg : a - n ∈ Gd
    · rw [if_pos hg, mul_one]
      obtain ⟨h1, h2⟩ := hGd2 (a - n) hg
      have := (abs_le.1 h1).1
      linarith
    · rw [if_neg hg, mul_zero]; exact hRHS0
  · rw [if_neg hs]
    have h01 : (if a - n ∈ Gd then (1 : ℝ) else 0) - 1 ≤ 0 := by split_ifs <;> norm_num
    have : 0 ≤ (9 / 10 - 2 * t) * (α0 * α1) := by
      have : 0 ≤ (9 / 10 - 2 * t) := by linarith
      positivity
    have := mul_nonpos_of_nonneg_of_nonpos this h01
    linarith

open Classical in
/-- **Proposition 9.10**, combinatorial part. -/
theorem dfA (ρv : ℝ) (ξ ξ' ξ'' : ZMod p → ZMod p) (Gd : Finset (ZMod p)) {t e5 e6 r' : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) (hr' : 0 < r') (hr4 : 4 * r' ≤ R j)
    (hGd1 : ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) ≤ e5)
    (hGd2 : ∀ a ∈ Gd, |g12 R A T c j a - alph R A T c j 0 * alph R A T c j 1| ≤
        alph R A T c j 0 * alph R A T c j 1 / 10 ∧
      ∑ x, regP T (R (j + 2)) x * (I12 A a (cent c 1 + x) *
        vb S ρv (ξ' a - ξ (a - (cent c 1 + x)) - ξ (cent c 1 + x))) ≤
        2 * t * (alph R A T c j 0 * alph R A T c j 1))
    (hsen : ∀ n, snorm T n ≤ r' → ∑ a, regP T (R j) (a - aC c) *
      (if Good S (8 * (1 / ρv)) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1) ≤ e6) :
    ∃ a0 ξ0 : ZMod p,
      (9 / 10 - 2 * t) * (alph R A T c j 0 * alph R A T c j 1) *
          (1 - e5 - 50 * T.card * r' / R j - e6) ≤
        ∑ n, regP T r' n * (ind (A 0) (a0 - n) *
          (if Good S (9 * (1 / ρv)) (ξ'' n + ξ (a0 - n) - ξ0) then 1 else 0)) ∧
      (0 < (9 / 10 - 2 * t) * (alph R A T c j 0 * alph R A T c j 1) *
          (1 - e5 - 50 * T.card * r' / R j - e6) →
        ∃ n, regP T r' n ≠ 0 ∧ a0 - n ∈ A 0) := by
  set α0 := alph R A T c j 0
  set α1 := alph R A T c j 1
  set Q := (9 / 10 - 2 * t) * (α0 * α1) * (1 - e5 - 50 * T.card * r' / R j - e6) with hQ
  have hα0 : 0 ≤ α0 := alph_nonneg R A T c j 0
  have hα1 : 0 ≤ α1 := alph_nonneg R A T c j 1
  have hPa := regP_center_isDist T (hR0 j).le (aC c)
  have hPn := regP_isDist T hr'.le
  have hP2 := regP_isDist T (hR0 (j + 2)).le
  set X : ZMod p → ZMod p → ZMod p → ℝ := fun a n x => I12 A (a - n) (cent c 1 + x) *
    (if Good S (9 * (1 / ρv)) (ξ' a - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x) - ξ'' n)
      then 1 else 0) with hX
  have hX0 : ∀ a n x, 0 ≤ X a n x := fun a n x =>
    mul_nonneg (I12_nonneg _ _ _) (by split_ifs <;> norm_num)
  -- lower bound for the total
  have hGdn : ∀ n, regP T r' n ≠ 0 → 1 - e5 - 50 * T.card * r' / R j ≤
      ∑ a, regP T (R j) (a - aC c) * (if a - n ∈ Gd then 1 else 0) := by
    intro n hn
    have hsn : snorm T (-n) ≤ r' := by
      rw [snorm_neg]; exact snorm_le_of_mem (mem_bohr_of_regP_ne_zero hr'.le hn) hr'.le
    have := shift_real_c subset_rfl (hR0 j) hr4 hsn (aC c) (B := (1 : ℝ))
      (fun a => if a ∈ Gd then (1 : ℝ) else 0) (fun a => by (try dsimp only); split_ifs <;> norm_num)
    simp only [one_mul] at this
    have e1 : ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then (1 : ℝ) else 0) =
        1 - ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) := by
      have h : ∀ a, regP T (R j) (a - aC c) * (if a ∈ Gd then (1 : ℝ) else 0) =
          regP T (R j) (a - aC c) - regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) :=
        fun a => by split_ifs <;> ring
      rw [sum_congr rfl fun a _ => h a, sum_sub_distrib, hPa.2]
    have e2 : ∀ a, (if a + -n ∈ Gd then (1 : ℝ) else 0) = if a - n ∈ Gd then 1 else 0 :=
      fun a => by rw [← sub_eq_add_neg]
    simp only [e2] at this
    have := (abs_le.1 this).1
    linarith
  have hsen' : ∑ n, regP T r' n * ∑ a, regP T (R j) (a - aC c) *
      (if Good S (8 * (1 / ρv)) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1) ≤ e6 :=
    wavg_le hPn.1 hPn.2 _ fun n hn =>
      hsen n (snorm_le_of_mem (mem_bohr_of_regP_ne_zero hr'.le hn) hr'.le)
  have hGd' : 1 - e5 - 50 * T.card * r' / R j ≤ ∑ n, regP T r' n *
      ∑ a, regP T (R j) (a - aC c) * (if a - n ∈ Gd then 1 else 0) :=
    le_wavg' hPn.1 hPn.2 _ hGdn
  have hc0 : 0 ≤ (9 / 10 - 2 * t) * (α0 * α1) := by
    have : 0 ≤ 9 / 10 - 2 * t := by linarith
    positivity
  have htot : Q ≤ ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
      ∑ n, regP T r' n * X a n x := by
    have hlow : ∑ a, regP T (R j) (a - aC c) * ∑ n, regP T r' n *
        ((9 / 10 - 2 * t) * (α0 * α1) * ((if a - n ∈ Gd then 1 else 0) -
          (if Good S (8 * (1 / ρv)) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1))) ≤
        ∑ a, regP T (R j) (a - aC c) * ∑ n, regP T r' n * ∑ x, regP T (R (j + 2)) x *
          X a n x :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (sum_le_sum fun n _ =>
        mul_le_mul_of_nonneg_left (dfA_pt hR0 ρv ξ ξ' ξ'' Gd ht ht1 hGd2 a n)
          (regP_nonneg _ _)) (regP_nonneg _ _)
    have e1 : ∑ a, regP T (R j) (a - aC c) * ∑ n, regP T r' n *
        ((9 / 10 - 2 * t) * (α0 * α1) * ((if a - n ∈ Gd then 1 else 0) -
          (if Good S (8 * (1 / ρv)) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1))) =
        (9 / 10 - 2 * t) * (α0 * α1) * (∑ n, regP T r' n *
          ∑ a, regP T (R j) (a - aC c) * (if a - n ∈ Gd then 1 else 0)) -
        (9 / 10 - 2 * t) * (α0 * α1) * ∑ n, regP T r' n * ∑ a, regP T (R j) (a - aC c) *
          (if Good S (8 * (1 / ρv)) (ξ' a - ξ' (a - n) - ξ'' n) then 0 else 1) := by
      rw [wswap, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun n _ => ?_
      simp only [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun a _ => by ring
    have e2 : ∀ a, ∑ n, regP T r' n * ∑ x, regP T (R (j + 2)) x * X a n x =
        ∑ x, regP T (R (j + 2)) x * ∑ n, regP T r' n * X a n x := fun a => wswap _ _ _
    simp_rw [e2] at hlow
    rw [e1] at hlow
    have := mul_le_mul_of_nonneg_left hGd' hc0
    have := mul_le_mul_of_nonneg_left hsen' hc0
    rw [hQ]; nlinarith
  obtain ⟨a, ha⟩ := exists_ge_wsum hPa.1 hPa.2 (fun a => ∑ x, regP T (R (j + 2)) x *
    ∑ n, regP T r' n * X a n x)
  obtain ⟨x, hx⟩ := exists_ge_wsum hP2.1 hP2.2 (fun x => ∑ n, regP T r' n * X a n x)
  have hQx : Q ≤ ∑ n, regP T r' n * X a n x := (htot.trans ha).trans hx
  refine ⟨a - (cent c 1 + x), ξ' a - ξ (cent c 1 + x), hQx.trans (sum_le_sum fun n _ =>
    mul_le_mul_of_nonneg_left ?_ (regP_nonneg _ _)), fun hQ0 => ?_⟩
  · simp only [hX, I12]
    have e : a - n - (cent c 1 + x) = a - (cent c 1 + x) - n := by ring
    have eg : ξ' a - ξ (a - n - (cent c 1 + x)) - ξ (cent c 1 + x) - ξ'' n =
        -(ξ'' n + ξ (a - (cent c 1 + x) - n) - (ξ' a - ξ (cent c 1 + x))) := by rw [e]; ring
    rw [eg, show a - n - (cent c 1 + x) = a - (cent c 1 + x) - n by ring]
    simp only [Good.iff_neg]
    have h1 := ind_nonneg (A 0) (a - (cent c 1 + x) - n)
    have h2 := ind_le_one (A 1) (cent c 1 + x)
    have h3 := ind_nonneg (A 1) (cent c 1 + x)
    split_ifs <;> nlinarith
  · by_contra hne
    push_neg at hne
    have : ∑ n, regP T r' n * X a n x ≤ 0 := by
      refine sum_nonpos fun n _ => ?_
      by_cases hn : regP T r' n = 0
      · rw [hn, zero_mul]
      · have hA : a - (cent c 1 + x) - n ∉ A 0 := hne n hn
        simp only [hX, I12, ind, show a - n - (cent c 1 + x) = a - (cent c 1 + x) - n by ring,
          if_neg hA]
        simp
    linarith

end dfA

end

end GT
end File_GT_U3S7b

section File_GT_U3S7c
/-!
# Local inverse `U³`, Proposition 9.10 (analytic part): refining the inner variable
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma sq_sub_sq_le_two_norm {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 + 2 * ‖u - v‖ := by
  have h1 : ‖u‖ - ‖v‖ ≤ ‖u - v‖ := norm_sub_norm_le u v
  have h2 : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u - v)]

/-- Refining the inner variable of a local `U²`-type correlation. -/
theorem inner_refine {S T : Finset (ZMod p)} (hST : S ⊆ T) {ρ0 ρ1 ρ5 : ℝ} (hρ1 : 0 < ρ1)
    (hρ5 : 0 < ρ5) (h41 : 4 * ρ1 ≤ ρ0) (h45 : 4 * ρ5 ≤ ρ1) (g : ZMod p → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) (lam : ZMod p) :
    ∑ n0, regP S ρ0 n0 * ‖∑ n1, (regP S ρ1 n1 : ℂ) * g (n0 + n1) * ech (lam * n1)‖ ^ 2 ≤
      ∑ n0, regP S ρ0 n0 * ‖∑ m, (regP T ρ5 m : ℂ) * g (n0 + m) * ech (lam * m)‖ ^ 2 +
        (2 * (50 * S.card * ρ5 / ρ1) + 50 * S.card * ρ1 / ρ0) := by
  have hρ0 : 0 < ρ0 := by linarith
  have hP0 := regP_isDist S hρ0.le
  have hP1 := regP_isDist S hρ1.le
  have hP5 := regP_isDist T hρ5.le
  set W : ZMod p → ℂ := fun y => ∑ m, (regP T ρ5 m : ℂ) * g (y + m) * ech (lam * m) with hW
  have hWb : ∀ y, ‖W y‖ ≤ 1 := fun y => by
    have := norm_wavg_le hP5.1 hP5.2 (fun m => g (y + m) * ech (lam * m)) (B := 1)
      (fun m _ => by rw [norm_mul, norm_ech, mul_one]; exact hg _)
    simpa [hW, mul_assoc] using this
  have key : ∀ n0, ‖∑ n1, (regP S ρ1 n1 : ℂ) * g (n0 + n1) * ech (lam * n1)‖ ^ 2 ≤
      ∑ n1, regP S ρ1 n1 * ‖W (n0 + n1)‖ ^ 2 + 2 * (50 * S.card * ρ5 / ρ1) := by
    intro n0
    set G : ZMod p → ℂ := fun y => g (n0 + y) * ech (lam * y) with hG
    have hGb : ∀ y, ‖G y‖ ≤ 1 := fun y => by
      rw [hG, norm_mul, norm_ech, mul_one]; exact hg _
    set U := ∑ n1, (regP S ρ1 n1 : ℂ) * g (n0 + n1) * ech (lam * n1) with hU
    set V := ∑ m, (regP T ρ5 m : ℂ) * ∑ n1, (regP S ρ1 n1 : ℂ) * G (n1 + m) with hV
    have hUV : ‖V - U‖ ≤ 50 * S.card * ρ5 / ρ1 := by
      have hUe : U = ∑ m, (regP T ρ5 m : ℂ) * ∑ n1, (regP S ρ1 n1 : ℂ) * G n1 := by
        rw [← sum_mul, ← Complex.ofReal_sum, hP5.2, Complex.ofReal_one, one_mul, hU]
        exact sum_congr rfl fun n1 _ => by rw [hG]; ring
      rw [hUe, hV, ← sum_sub_distrib]
      simp_rw [← mul_sub]
      refine norm_wavg_le hP5.1 hP5.2 _ fun m hm => ?_
      have hs : snorm S m ≤ ρ5 :=
        (snorm_mono hST m).trans (snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ5.le hm) hρ5.le)
      have := shift_cplx_c subset_rfl hρ1 h45 hs 0 (B := 1) G hGb
      simpa using this
    have hVe : V = ∑ n1, (regP S ρ1 n1 : ℂ) * (ech (lam * n1) * W (n0 + n1)) := by
      rw [hV, hW]
      simp only [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun n1 _ => sum_congr rfl fun m _ => ?_
      rw [hG]; simp only
      rw [show lam * (n1 + m) = lam * n1 + lam * m by ring, ech_add,
        show n0 + (n1 + m) = n0 + n1 + m by ring]
      ring
    have hVb : ‖V‖ ^ 2 ≤ ∑ n1, regP S ρ1 n1 * ‖W (n0 + n1)‖ ^ 2 := by
      rw [hVe]
      refine (norm_wsum_sq_le hP1.1 hP1.2 _).trans (le_of_eq (sum_congr rfl fun n1 _ => ?_))
      rw [norm_mul, norm_ech, one_mul]
    have hUb : ‖U‖ ≤ 1 := by
      have := norm_wavg_le hP1.1 hP1.2 (fun n1 => g (n0 + n1) * ech (lam * n1)) (B := 1)
        (fun m _ => by rw [norm_mul, norm_ech, mul_one]; exact hg _)
      simpa [hU, mul_assoc] using this
    have hVb1 : ‖V‖ ≤ 1 := by
      rw [hVe]
      have := norm_wavg_le hP1.1 hP1.2 (fun n1 => ech (lam * n1) * W (n0 + n1)) (B := 1)
        (fun m _ => by rw [norm_mul, norm_ech, one_mul]; exact hWb _)
      simpa using this
    have := sq_sub_sq_le_two_norm hUb hVb1
    rw [norm_sub_rev] at hUV
    linarith
  calc _ ≤ ∑ n0, regP S ρ0 n0 * (∑ n1, regP S ρ1 n1 * ‖W (n0 + n1)‖ ^ 2 +
        2 * (50 * S.card * ρ5 / ρ1)) :=
        sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left (key n0) (hP0.1 n0)
    _ = ∑ n1, regP S ρ1 n1 * ∑ n0, regP S ρ0 n0 * ‖W (n0 + n1)‖ ^ 2 +
        2 * (50 * S.card * ρ5 / ρ1) := by
        rw [wavg_add_const hP0.2]
        congr 1
        exact wswap _ _ _
    _ ≤ ∑ n1, regP S ρ1 n1 * (∑ n0, regP S ρ0 n0 * ‖W n0‖ ^ 2 + 50 * S.card * ρ1 / ρ0) +
        2 * (50 * S.card * ρ5 / ρ1) := by
        refine add_le_add_left (sum_le_sum fun n1 _ => ?_) _
        by_cases hn1 : regP S ρ1 n1 = 0
        · rw [hn1, zero_mul, zero_mul]
        refine mul_le_mul_of_nonneg_left ?_ (hP1.1 n1)
        have hs : snorm S n1 ≤ ρ1 :=
          snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ1.le hn1) hρ1.le
        have := shift_real subset_rfl hρ0 h41 hs (fun y => ‖W y‖ ^ 2) (B := 1)
          (fun y => by
            rw [abs_of_nonneg (sq_nonneg _)]
            exact pow_le_one₀ (norm_nonneg _) (hWb y))
        have := (abs_le.1 this).2
        linarith
    _ = _ := by rw [wavg_add_const hP1.2, ← sum_mul, hP1.2, one_mul]; ring

/-- Replacing a phase by a nearby one on a small Bohr set. -/
lemma phase_close {T : Finset (ZMod p)} {ρ5 : ℝ} (hρ5 : 0 < ρ5) (g : ZMod p → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) (lam lam' : ZMod p) {ε : ℝ}
    (h : ∀ m, regP T ρ5 m ≠ 0 → cn ((lam - lam') * m) ≤ ε) (y : ZMod p) :
    ‖∑ m, (regP T ρ5 m : ℂ) * g (y + m) * ech (lam * m)‖ ^ 2 ≤
      ‖∑ m, (regP T ρ5 m : ℂ) * g (y + m) * ech (lam' * m)‖ ^ 2 + 2 * (2 * Real.pi * ε) := by
  have hP5 := regP_isDist T hρ5.le
  have hb : ∀ l : ZMod p, ‖∑ m, (regP T ρ5 m : ℂ) * g (y + m) * ech (l * m)‖ ≤ 1 := fun l => by
    have := norm_wavg_le hP5.1 hP5.2 (fun m => g (y + m) * ech (l * m)) (B := 1)
      (fun m _ => by rw [norm_mul, norm_ech, mul_one]; exact hg _)
    simpa [mul_assoc] using this
  refine (sq_sub_sq_le_two_norm (hb lam) (hb lam')).trans (add_le_add le_rfl ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← sum_sub_distrib]
  have e : ∀ m, (regP T ρ5 m : ℂ) * g (y + m) * ech (lam * m) -
      (regP T ρ5 m : ℂ) * g (y + m) * ech (lam' * m) =
      (regP T ρ5 m : ℂ) * (g (y + m) * ech (lam' * m) * (ech ((lam - lam') * m) - 1)) := by
    intro m
    rw [show lam * m = lam' * m + (lam - lam') * m by ring, ech_add]; ring
  simp_rw [e]
  refine norm_wavg_le hP5.1 hP5.2 _ fun m hm => ?_
  rw [norm_mul, norm_mul, norm_ech, mul_one]
  calc ‖g (y + m)‖ * ‖ech ((lam - lam') * m) - 1‖ ≤ 1 * (2 * Real.pi * ε) :=
        mul_le_mul (hg _) ((norm_ech_sub_one_le _).trans (mul_le_mul_of_nonneg_left (h m hm)
          (by positivity))) (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

open Classical in
/-- **Proposition 9.10** (analytic part). -/
theorem dfB {S T : Finset (ZMod p)} (hST : S ⊆ T) {ρ0 ρ1 ρ5 r' η Bg Q : ℝ} (hρ1 : 0 < ρ1)
    (hρ5 : 0 < ρ5) (h41 : 4 * ρ1 ≤ ρ0) (h45 : 4 * ρ5 ≤ ρ1) (hBg : 0 ≤ Bg)
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (Ω A0 : Finset (ZMod p)) (hA0 : A0 ⊆ Ω)
    (ξ ξ'' : ZMod p → ZMod p) (a0 ξ0 : ZMod p)
    (hΩ : ∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
      ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
        ech (-(ξ D * n1))‖ ^ 2)
    (hQ : Q ≤ ∑ n, regP T r' n * (ind A0 (a0 - n) *
      (if Good S Bg (ξ'' n + ξ (a0 - n) - ξ0) then 1 else 0)))
    (hz : 0 ≤ η / 8 - (2 * (50 * S.card * ρ5 / ρ1) + 50 * S.card * ρ1 / ρ0) -
      2 * (2 * Real.pi * (Bg * ρ5))) :
    Q * (η / 8 - (2 * (50 * S.card * ρ5 / ρ1) + 50 * S.card * ρ1 / ρ0) -
      2 * (2 * Real.pi * (Bg * ρ5))) ≤
      ∑ n, regP T r' n * ∑ n0, regP S ρ0 n0 *
        ‖∑ m, (regP T ρ5 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
          ech ((ξ'' n - ξ0) * m)‖ ^ 2 := by
  set z0 := η / 8 - (2 * (50 * S.card * ρ5 / ρ1) + 50 * S.card * ρ1 / ρ0) -
      2 * (2 * Real.pi * (Bg * ρ5)) with hz0
  have hρ0 : 0 < ρ0 := by linarith
  have hP0 := regP_isDist S hρ0.le
  set Z : ZMod p → ℝ := fun n => ∑ n0, regP S ρ0 n0 *
      ‖∑ m, (regP T ρ5 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
        ech ((ξ'' n - ξ0) * m)‖ ^ 2 with hZ
  have hZ0 : ∀ n, 0 ≤ Z n := fun n =>
    sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _) (sq_nonneg _)
  have hpt : ∀ n, (ind A0 (a0 - n) * (if Good S Bg (ξ'' n + ξ (a0 - n) - ξ0) then 1 else 0)) *
      z0 ≤ Z n := by
    intro n
    by_cases h1 : a0 - n ∈ A0
    · by_cases h2 : Good S Bg (ξ'' n + ξ (a0 - n) - ξ0)
      · rw [if_pos h2, ind, if_pos h1, one_mul, one_mul]
        set D := a0 - n
        set g : ZMod p → ℂ := fun y => f (y + D) * conj (f y) with hg
        have hgb : ∀ y, ‖g y‖ ≤ 1 := fun y => by
          rw [hg, norm_mul, Complex.norm_conj]
          exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
        have h3 := hΩ D (hA0 h1)
        have h4 := inner_refine hST hρ1 hρ5 h41 h45 g hgb (-ξ D)
        have e1 : ∀ n0, ∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
            ech (-(ξ D * n1)) = ∑ n1, (regP S ρ1 n1 : ℂ) * g (n0 + n1) * ech (-ξ D * n1) :=
          fun n0 => sum_congr rfl fun n1 _ => by rw [hg, neg_mul]
        simp_rw [e1] at h3
        have h5 : ∀ n0, ‖∑ m, (regP T ρ5 m : ℂ) * g (n0 + m) * ech (-ξ D * m)‖ ^ 2 ≤
            ‖∑ m, (regP T ρ5 m : ℂ) * g (n0 + m) * ech ((ξ'' n - ξ0) * m)‖ ^ 2 +
              2 * (2 * Real.pi * (Bg * ρ5)) := by
          intro n0
          refine phase_close hρ5 g hgb _ _ (fun m hm => ?_) n0
          have hsm : snorm S m ≤ ρ5 := (snorm_mono hST m).trans
            (snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ5.le hm) hρ5.le)
          have := h2 m
          have e : (-ξ D - (ξ'' n - ξ0)) * m = -((ξ'' n + ξ (a0 - n) - ξ0) * m) := by ring
          rw [e, cn_neg]
          exact this.trans (mul_le_mul_of_nonneg_left hsm hBg)
        have h6 : ∑ n0, regP S ρ0 n0 * ‖∑ m, (regP T ρ5 m : ℂ) * g (n0 + m) * ech (-ξ D * m)‖ ^ 2
            ≤ Z n + 2 * (2 * Real.pi * (Bg * ρ5)) := by
          calc _ ≤ ∑ n0, regP S ρ0 n0 *
                (‖∑ m, (regP T ρ5 m : ℂ) * g (n0 + m) * ech ((ξ'' n - ξ0) * m)‖ ^ 2 +
                  2 * (2 * Real.pi * (Bg * ρ5))) :=
                sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left (h5 n0) (hP0.1 n0)
            _ = _ := by
                rw [wavg_add_const hP0.2]
        linarith
      · rw [if_neg h2, mul_zero, zero_mul]; exact hZ0 n
    · rw [ind, if_neg h1, zero_mul, zero_mul]; exact hZ0 n
  calc Q * z0 ≤ (∑ n, regP T r' n * (ind A0 (a0 - n) *
        (if Good S Bg (ξ'' n + ξ (a0 - n) - ξ0) then 1 else 0))) * z0 :=
        mul_le_mul_of_nonneg_right hQ hz
    _ = ∑ n, regP T r' n * ((ind A0 (a0 - n) *
        (if Good S Bg (ξ'' n + ξ (a0 - n) - ξ0) then 1 else 0)) * z0) := by
        rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ _ := sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hpt n) (regP_nonneg _ _)

end

end GT
end File_GT_U3S7c

section File_GT_U3Mid
/-!
# Local inverse `U³`: steps four to six combined

From the penalised weight of the third step we pass to a pseudorandom neighbourhood (fourth step),
construct `ξ'` (fifth step), `ξ''` (sixth step) and derive the correlation estimate of
Proposition 9.10.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma abs_Wt_le (S : Finset (ZMod p)) (ρv : ℝ) {L : ℝ} (hL : 1 ≤ L) (ξ : ZMod p → ZMod p)
    (A : Fin 4 → Finset (ZMod p)) (q : Fin 4 → ZMod p) : |Wt S ρv L ξ A q| ≤ L := by
  unfold Wt
  split_ifs
  all_goals first
    | (norm_num; linarith)
    | (norm_num; rw [abs_le]; constructor <;> linarith)
    | linarith

lemma Wt_le_one (S : Finset (ZMod p)) (ρv : ℝ) {L : ℝ} (hL : 1 ≤ L) (ξ : ZMod p → ZMod p)
    (A : Fin 4 → Finset (ZMod p)) (q : Fin 4 → ZMod p) : Wt S ρv L ξ A q ≤ 1 := by
  unfold Wt
  split_ifs <;> simp <;> linarith

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Steps four to six combined**, with `t = 1/200`. -/
theorem u3_mid {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) (hR1 : R 0 ≤ 1)
    {S : Finset (ZMod p)} (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {ρ0 ρ1 ρ2 η : ℝ} (hη : 0 < η) (hρ1 : 0 < ρ1) (hρ2 : 0 ≤ ρ2)
    (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (hΩb : ∀ D ∈ Ω, D ∈ bohr S (2 * ρ2))
    (hΩ : ∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
      ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
        ech (-(ξ D * n1))‖ ^ 2)
    (As : Fin 4 → Finset (ZMod p)) (hAs : ∀ i, As i ⊆ Ω) {ρv L : ℝ} (hρv : 0 < ρv) (hL : 1 ≤ L)
    (c0 : Fin 4 → ZMod p) {c3 ε mu : ℝ} {K : ℕ}
    (hc3 : 0 < c3) (hε : 0 < ε) (hmu : 0 < mu) (hQ0 : c3 ≤ QW R (Wt S ρv L ξ As) S c0 0)
    -- fourth step
    (hmuε : 20 * mu ≤ c3 / 8 * (ε / 8) ^ 2 / 4) (hK : 1 + 20 * mu ≤ 20 * mu * K)
    (hθK : (L * 300 + c3 / 8 * 1600) * (S.card + K) * θ ≤ c3 / 8 * (ε / 8) ^ 2 / 4)
    (hsep : 7200 * (S.card + K) * θ ≤ (ε / 2) ^ 2)
    (herr : (350 * (S.card + K) + 13) * θ ≤ ε / 8)
    -- fifth step
    (h5a : L * (50 * (S.card + K) * θ) ≤ c3 / 4)
    (h5b : 2 * √(√ε + 200 * (S.card + K) * θ) ≤ c3 / 8)
    (h5c : 2 / (L * (1 / 200)) + 1700 * (√ε + 200 * (S.card + K) * θ) / (c3 / 2) ^ 2 ≤ 1 / 1000)
    (hep : 30 * (√(√ε + 200 * (S.card + K) * θ) + 150 * (S.card + K) * θ) / (c3 / 8) ^ 2 ≤
      1 / 1000)
    -- sixth step and Proposition 9.10
    {r r' ρ4 : ℝ} (hr' : 0 < r') (hr'r : r' ≤ r) (hr4 : 4 * r ≤ R (20 * K))
    (hrK : 50 * (S.card + K) * r / R (20 * K) ≤ 1 / 1000)
    (hρ4 : 0 < ρ4) (h41 : 4 * ρ1 ≤ ρ0) (h44 : 4 * ρ4 ≤ ρ1)
    (hz : 2 * (50 * S.card * ρ4 / ρ1) + 50 * S.card * ρ1 / ρ0 + 2 * (2 * Real.pi * (9 * (1 / ρv) * ρ4))
      ≤ η / 16) :
    ∃ (T : Finset (ZMod p)) (k : ℕ) (ξ'' : ZMod p → ZMod p) (a0 ξ0 : ZMod p),
      S ⊆ T ∧ T.card ≤ S.card + k ∧ k < K ∧
      (∀ x y, snorm T x ≤ r / 2 → snorm T y ≤ r / 2 →
        Good T (24 * (1 / ρv)) (ξ'' (x + y) - ξ'' x - ξ'' y)) ∧
      snorm S a0 ≤ 2 * ρ2 + r' ∧
      c3 * η / 288 ≤ ∑ n, regP T r' n * ∑ n0, regP S ρ0 n0 *
        ‖∑ m, (regP T ρ4 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
          ech ((ξ'' n - ξ0) * m)‖ ^ 2 := by
  have hθ1' : θ ≤ 1 := by linarith
  -- fourth step
  obtain ⟨c, k, T, hST, hTc, hkK, hQ4, hPR⟩ := u3_step4 hR0 hRk hθ0 hθ1 hR1 S
    (Wt S ρv L ξ As) (abs_Wt_le S ρv hL ξ As) (Wt_le_one S ρv hL ξ As) As c0 hc3 hε hmu hQ0
    hmuε hK hθK hsep herr
  set j := 20 * k with hj
  have hTK : (T.card : ℝ) ≤ S.card + K := by
    have : (T.card : ℝ) ≤ S.card + k := by exact_mod_cast hTc
    have : (k : ℝ) ≤ K := by exact_mod_cast hkK.le
    linarith
  have hθ0' : 0 ≤ (T.card : ℝ) * θ := by positivity
  have hTθ : (T.card : ℝ) * θ ≤ (S.card + K) * θ := mul_le_mul_of_nonneg_right hTK hθ0
  -- fifth step
  have h1 : L * (50 * T.card * θ) ≤ c3 / 2 / 2 := by nlinarith
  have hsq : √(√ε + 200 * T.card * θ) ≤ √(√ε + 200 * (S.card + K) * θ) := by
    apply Real.sqrt_le_sqrt; nlinarith
  have h2 : 2 * √(√ε + 200 * T.card * θ) ≤ c3 / 2 / 4 := by linarith
  have ht : (0 : ℝ) < 1 / 200 := by norm_num
  have hL0 : 0 < L := by linarith
  obtain ⟨Gd, ξ', hα, hGd1, hGd2⟩ := u3_step5 hR0 hRk hθ0 hθ1 hPR S ρv L ξ
    (abs_Wt_le S ρv hL ξ As) (by positivity : (0 : ℝ) < c3 / 2) ht hL0 hQ4 h1 h2
  set α0 := alph R As T c j 0
  set α1 := alph R As T c j 1
  have hα0 : 0 ≤ α0 := alph_nonneg R As T c j 0
  have hα1 : 0 ≤ α1 := alph_nonneg R As T c j 1
  have hα2 : 0 ≤ alph R As T c j 2 := alph_nonneg R As T c j 2
  have hα3 : 0 ≤ alph R As T c j 3 := alph_nonneg R As T c j 3
  have hα2' : alph R As T c j 2 ≤ 1 := alph_le_one As T c j 2 (hR0 _).le
  have hα3' : alph R As T c j 3 ≤ 1 := alph_le_one As T c j 3 (hR0 _).le
  have hαα : c3 / 8 ≤ α0 * α1 := by
    have h23 : alph R As T c j 2 * alph R As T c j 3 ≤ 1 := mul_le_one₀ hα2' hα3 hα3'
    have := mul_le_mul_of_nonneg_left h23 (mul_nonneg hα0 hα1)
    linarith
  have hpos : 0 < α0 * α1 := by linarith
  set e5 := 2 / (L * (1 / 200)) + 1700 * (√ε + 200 * T.card * θ) / (c3 / 2) ^ 2 with he5
  have he5 : e5 ≤ 1 / 1000 := by
    refine le_trans ?_ h5c
    rw [he5]
    gcongr
  have he50 : 0 ≤ e5 := by positivity
  -- pordo
  have hE := pordo hR0 hRk hθ0 hθ1 hPR S ρv ξ ξ' Gd ht.le hpos hGd1 (fun a ha => (hGd2 a ha).2)
  set ep := 8 * (2 * (1 / 200) + e5) + 30 * (√(√ε + 200 * T.card * θ) + 150 * T.card * θ) /
    (α0 * α1) ^ 2 with hep_def
  have hep' : ep ≤ 8 * (2 * (1 / 200) + 1 / 1000) + 1 / 1000 := by
    have h30 : 30 * (√(√ε + 200 * T.card * θ) + 150 * T.card * θ) / (α0 * α1) ^ 2 ≤
        30 * (√(√ε + 200 * (S.card + K) * θ) + 150 * (S.card + K) * θ) / (c3 / 8) ^ 2 := by
      gcongr
    rw [hep_def]; linarith
  have hep0 : 0 ≤ ep := by positivity
  -- majority
  have hRj : R (20 * K) ≤ R j := R_anti hR0 hRk hθ0 hθ1' (by omega)
  have hRj3 : R (20 * K) ≤ R (j + 3) := R_anti hR0 hRk hθ0 hθ1' (by omega)
  have hr0 : 0 < r := lt_of_lt_of_le hr' hr'r
  have hRK0 := hR0 (20 * K)
  have hq1 : 50 * T.card * r / R j ≤ 1 / 1000 := by
    refine le_trans ?_ hrK
    have : 0 ≤ 50 * (T.card : ℝ) * r := by positivity
    calc 50 * T.card * r / R j ≤ 50 * T.card * r / R (20 * K) := by gcongr
      _ ≤ _ := by gcongr
  have hq2 : 50 * T.card * r / R (j + 3) ≤ 1 / 1000 := by
    refine le_trans ?_ hrK
    have : 0 ≤ 50 * (T.card : ℝ) * r := by positivity
    calc 50 * T.card * r / R (j + 3) ≤ 50 * T.card * r / R (20 * K) := by gcongr
      _ ≤ _ := by gcongr
  have hq3 : 50 * T.card * (r / 2) / R j ≤ 1 / 1000 := by
    have : 50 * T.card * (r / 2) / R j = (50 * T.card * r / R j) / 2 := by ring
    have : 0 ≤ 50 * (T.card : ℝ) * r / R j := by have := hR0 j; positivity
    linarith
  have hE' : ∑ h, regP T (R (j + 3)) h * ∑ a, regP T (R j) (a - aC c) *
      ∑ b, regP T (R j) (b - aC c) *
      (if Good S (4 * (1 / ρv)) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h)) then 0 else 1) ≤ ep := by
    have e : 4 * (1 / ρv) = 4 / ρv := by ring
    rw [e]; exact hE
  obtain ⟨ξ'', hsen, hlin⟩ := majority (hR0 j) (hR0 (j + 3)) (aC c) ξ' (1 / ρv)
    (le_trans hr4 hRj) (le_trans hr4 hRj3) hE' (by linarith)
  set e6 := 2 * ep + (50 * T.card * r / R j + 50 * T.card * r / R (j + 3)) with he6
  -- Proposition 9.10, combinatorial part
  have hr'4 : 4 * r' ≤ R j := by linarith
  obtain ⟨a0, ξ0, hQA, hex⟩ := dfA hR0 ρv ξ ξ' ξ'' Gd ht.le (by norm_num) hr' hr'4 hGd1
    (fun a ha => hGd2 a ha) (fun n hn => hsen n (hn.trans hr'r))
  have hr'R : 50 * T.card * r' / R j ≤ 1 / 1000 := by
    refine le_trans ?_ hq1
    have := hR0 j
    gcongr
  have hbr : 1 / 2 ≤ 1 - e5 - 50 * T.card * r' / R j - e6 := by
    rw [he6]; linarith
  set QA := (9 / 10 - 2 * (1 / 200)) * (α0 * α1) * (1 - e5 - 50 * T.card * r' / R j - e6)
    with hQA_def
  have hQA0 : c3 / 18 ≤ QA := by
    rw [hQA_def]
    have : (9 / 10 - 2 * (1 / 200) : ℝ) * (c3 / 8) * (1 / 2) ≤
        (9 / 10 - 2 * (1 / 200)) * (α0 * α1) * (1 - e5 - 50 * T.card * r' / R j - e6) := by
      gcongr
    linarith
  -- the location of `a0`
  obtain ⟨n, hn, hna⟩ := hex (by linarith)
  have hsa0 : snorm S a0 ≤ 2 * ρ2 + r' := by
    have e : a0 = (a0 - n) + n := by ring
    rw [e]
    refine (snorm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact snorm_le_of_mem (hΩb _ (hAs 0 hna)) (by linarith)
    · exact (snorm_mono hST n).trans
        (snorm_le_of_mem (mem_bohr_of_regP_ne_zero hr'.le hn) hr'.le)
  -- Proposition 9.10, analytic part
  have hz0 : 0 ≤ η / 8 - (2 * (50 * S.card * ρ4 / ρ1) + 50 * S.card * ρ1 / ρ0) -
      2 * (2 * Real.pi * (9 * (1 / ρv) * ρ4)) := by
    have : 0 ≤ 2 * (2 * Real.pi * (9 * (1 / ρv) * ρ4)) := by positivity
    have : 0 ≤ 2 * (50 * S.card * ρ4 / ρ1) + 50 * S.card * ρ1 / ρ0 := by
      have : 0 < ρ0 := by linarith
      positivity
    have : 0 ≤ η := by linarith
    linarith
  have hB9 : (0 : ℝ) ≤ 9 * (1 / ρv) := by positivity
  have hdfB := dfB hST hρ1 hρ4 h41 h44 hB9 f hf Ω (As 0) (hAs 0) ξ ξ'' a0 ξ0 hΩ hQA hz0
  refine ⟨T, k, ξ'', a0, ξ0, hST, hTc, hkK, fun x y hx hy => ?_, hsa0, le_trans ?_ hdfB⟩
  · exact (hlin x y hx hy).mono_set hST (by positivity)
  · have hη : η / 16 ≤ η / 8 - (2 * (50 * S.card * ρ4 / ρ1) + 50 * S.card * ρ1 / ρ0) -
        2 * (2 * Real.pi * (9 * (1 / ρv) * ρ4)) := by linarith
    have hη0 : 0 ≤ η := by linarith
    calc c3 * η / 288 = c3 / 18 * (η / 16) := by ring
      _ ≤ QA * (η / 16) := by gcongr
      _ ≤ _ := by gcongr

end

end GT
end File_GT_U3Mid

open Finset KM
open scoped ComplexConjugate
open Classical
open GT in
theorem solution {p : ℕ} [NeZero p] {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) (hR1 : R 0 ≤ 1)
    {S : Finset (ZMod p)} (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {ρ0 ρ1 ρ2 η : ℝ} (hη : 0 < η) (hρ1 : 0 < ρ1) (hρ2 : 0 ≤ ρ2)
    (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (hΩb : ∀ D ∈ Ω, D ∈ bohr S (2 * ρ2))
    (hΩ : ∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
      ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
        ech (-(ξ D * n1))‖ ^ 2)
    (As : Fin 4 → Finset (ZMod p)) (hAs : ∀ i, As i ⊆ Ω) {ρv L : ℝ} (hρv : 0 < ρv) (hL : 1 ≤ L)
    (c0 : Fin 4 → ZMod p) {c3 ε mu : ℝ} {K : ℕ}
    (hc3 : 0 < c3) (hε : 0 < ε) (hmu : 0 < mu) (hQ0 : c3 ≤ QW R (Wt S ρv L ξ As) S c0 0)
    -- fourth step
    (hmuε : 20 * mu ≤ c3 / 8 * (ε / 8) ^ 2 / 4) (hK : 1 + 20 * mu ≤ 20 * mu * K)
    (hθK : (L * 300 + c3 / 8 * 1600) * (S.card + K) * θ ≤ c3 / 8 * (ε / 8) ^ 2 / 4)
    (hsep : 7200 * (S.card + K) * θ ≤ (ε / 2) ^ 2)
    (herr : (350 * (S.card + K) + 13) * θ ≤ ε / 8)
    -- fifth step
    (h5a : L * (50 * (S.card + K) * θ) ≤ c3 / 4)
    (h5b : 2 * √(√ε + 200 * (S.card + K) * θ) ≤ c3 / 8)
    (h5c : 2 / (L * (1 / 200)) + 1700 * (√ε + 200 * (S.card + K) * θ) / (c3 / 2) ^ 2 ≤ 1 / 1000)
    (hep : 30 * (√(√ε + 200 * (S.card + K) * θ) + 150 * (S.card + K) * θ) / (c3 / 8) ^ 2 ≤
      1 / 1000)
    -- sixth step and Proposition 9.10
    {r r' ρ4 : ℝ} (hr' : 0 < r') (hr'r : r' ≤ r) (hr4 : 4 * r ≤ R (20 * K))
    (hrK : 50 * (S.card + K) * r / R (20 * K) ≤ 1 / 1000)
    (hρ4 : 0 < ρ4) (h41 : 4 * ρ1 ≤ ρ0) (h44 : 4 * ρ4 ≤ ρ1)
    (hz : 2 * (50 * S.card * ρ4 / ρ1) + 50 * S.card * ρ1 / ρ0 + 2 * (2 * Real.pi * (9 * (1 / ρv) * ρ4))
      ≤ η / 16) :
    ∃ (T : Finset (ZMod p)) (k : ℕ) (ξ'' : ZMod p → ZMod p) (a0 ξ0 : ZMod p),
      S ⊆ T ∧ T.card ≤ S.card + k ∧ k < K ∧
      (∀ x y, snorm T x ≤ r / 2 → snorm T y ≤ r / 2 →
        Good T (24 * (1 / ρv)) (ξ'' (x + y) - ξ'' x - ξ'' y)) ∧
      snorm S a0 ≤ 2 * ρ2 + r' ∧
      c3 * η / 288 ≤ ∑ n, regP T r' n * ∑ n0, regP S ρ0 n0 *
        ‖∑ m, (regP T ρ4 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
          ech ((ξ'' n - ξ0) * m)‖ ^ 2 :=
  @GT.u3_mid p _ R θ hR0 hRk hθ0 hθ1 hR1 S f hf ρ0 ρ1 ρ2 η hη hρ1 hρ2 Ω ξ hΩb hΩ As hAs ρv L hρv hL c0 c3 ε mu K hc3 hε hmu hQ0 hmuε hK hθK hsep herr h5a h5b h5c hep r r' ρ4 hr' hr'r hr4 hrK hρ4 h41 h44 hz

