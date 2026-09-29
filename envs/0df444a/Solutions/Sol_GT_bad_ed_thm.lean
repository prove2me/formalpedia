-- Prove2me | solution 1 for GT.bad_ed_thm
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:52.995681+00:00
-- url     : https://prove2.me/submissions/d75c5266-3450-448c-b154-7ee9a7837659

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_ed_num
import Theorems.Thm_GT_inv_u3

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

lemma bohr_image_mul (Γ : Finset (ZMod N)) {u v : ZMod N} (huv : u * v = 1) (ρ : ℝ) :
    bohr (Γ.image (· * v)) ρ = (bohr Γ ρ).image (u * ·) := by
  ext x
  simp only [mem_bohr, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h
    refine ⟨v * x, fun γ hγ => ?_, ?_⟩
    · have := h γ hγ; rwa [mul_assoc] at this
    · rw [← mul_assoc, huv, one_mul]
  · rintro ⟨y, hy, rfl⟩ γ hγ
    have : γ * v * (u * y) = γ * y := by
      rw [mul_assoc, ← mul_assoc v, mul_comm v u, huv, one_mul]
    rw [this]; exact hy γ hγ

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

lemma norm_toCircle_sub_one_le (s : ℝ) :
    ‖((AddCircle.toCircle (s : UnitAddCircle) : Circle) : ℂ) - 1‖ ≤ 2 * Real.pi * |s| := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_two]
  have := Real.abs_sin_le_abs (x := 2 * Real.pi / 1 * s / 2)
  have hpi := Real.pi_pos
  calc 2 * |Real.sin (2 * Real.pi / 1 * s / 2)| ≤ 2 * |2 * Real.pi / 1 * s / 2| := by linarith
    _ = 2 * Real.pi * |s| := by
      rw [div_one, mul_div_assoc, abs_mul, abs_div, abs_two, abs_mul, abs_two, abs_of_pos hpi]; ring

lemma norm_toCircle_sub_le (s s' : ℝ) :
    ‖((AddCircle.toCircle (s : UnitAddCircle) : Circle) : ℂ) -
      ((AddCircle.toCircle (s' : UnitAddCircle) : Circle) : ℂ)‖ ≤ 2 * Real.pi * |s - s'| := by
  have e : ((AddCircle.toCircle (s : UnitAddCircle) : Circle) : ℂ) =
      ((AddCircle.toCircle (s' : UnitAddCircle) : Circle) : ℂ) *
        ((AddCircle.toCircle ((s - s' : ℝ) : UnitAddCircle) : Circle) : ℂ) := by
    rw [← Circle.coe_mul, ← AddCircle.toCircle_add, ← AddCircle.coe_add]; ring_nf
  rw [e, ← mul_sub_one, norm_mul, Circle.norm_coe, one_mul]
  exact norm_toCircle_sub_one_le _

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

lemma ec_add (x y : UnitAddCircle) : ec (x + y) = ec x * ec y := by
  simp [ec, AddCircle.toCircle_add]

lemma ec_neg (x : UnitAddCircle) : ec (-x) = conj (ec x) := by
  rw [ec, ec, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

@[simp] lemma norm_ec (x : UnitAddCircle) : ‖ec x‖ = 1 := Circle.norm_coe _

lemma ec_coe (s : ℝ) : ec (s : UnitAddCircle) = Complex.exp (Complex.I * ((2 * Real.pi * s : ℝ) : ℂ)) := by
  rw [ec, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1; push_cast; ring

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

lemma snorm_nsmul_le (n : ℕ) (h : ZMod N) : snorm S ((n : ZMod N) * h) ≤ n * snorm S h := by
  rw [snorm_le_iff (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (snorm_nonneg h))]
  intro s hs
  rw [mul_left_comm]
  exact (cn_natCast_mul_le n _).trans
    (mul_le_mul_of_nonneg_left (cn_le_snorm hs h) (Nat.cast_nonneg (α := ℝ) n))

lemma snorm_intsmul_le (n : ℤ) (h : ZMod N) :
    snorm S ((n : ZMod N) * h) ≤ |(n : ℝ)| * snorm S h := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have := snorm_nsmul_le (S := S) m h
    simpa using this
  · have := snorm_nsmul_le (S := S) m h
    simpa [neg_mul] using this

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

/-- Pigeonhole: a weighted average is attained or exceeded at a point of positive weight. -/
lemma exists_pos_ge (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (F : α → ℝ) {c : ℝ}
    (h : c ≤ ∑ x, P x * F x) : ∃ x, P x ≠ 0 ∧ c ≤ F x := by
  by_contra hc
  push_neg at hc
  obtain ⟨x0, hx0⟩ : ∃ x, P x ≠ 0 := by
    by_contra h'; push_neg at h'; simp [h'] at hP1
  have hlt : ∑ x, P x * F x < ∑ x, P x * c := by
    apply sum_lt_sum
    · intro x _
      by_cases hx : P x = 0
      · rw [hx, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (hc x hx).le (hP x)
    · exact ⟨x0, mem_univ _, mul_lt_mul_of_pos_left (hc x0 hx0)
        (lt_of_le_of_ne (hP x0) (Ne.symm hx0))⟩
  rw [← sum_mul, hP1, one_mul] at hlt
  linarith

end avg

end

end GT
end File_GT_Prob

section File_GT_Lattice
/-!
# Gram determinants and reduced lattice bases

Toolkit for lattices `⊕ ℤ v_i` in a real inner product space:
* the Gram determinant transforms by `det(M)^2` under a change of family `v ↦ M v`;
* orthogonal splitting `det Gram(x, w) = ‖x‖² det Gram(w)` when `x ⊥ w`;
* Hadamard's inequality `det Gram(v) ≤ ∏ ‖v_i‖²`;
* the coordinate bound `|t_i| √det Gram(v) ≤ ‖∑ t_j v_j‖ ∏_{j ≠ i} ‖v_j‖`;
* completion of a primitive integer vector to a unimodular matrix;
* Hermite reduction: every lattice has a basis with `(∏‖b_i‖)² ≤ 2^{r²} det Gram`.
-/

open Finset Matrix

namespace GT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The family `M v : i ↦ ∑_j M i j • v j`. -/
def mixF {r s : ℕ} (M : Matrix (Fin r) (Fin s) ℝ) (v : Fin s → E) : Fin r → E :=
  fun i => ∑ j, M i j • v j

lemma gram_mixF {r s : ℕ} (M : Matrix (Fin r) (Fin s) ℝ) (v : Fin s → E) :
    Matrix.gram ℝ (mixF M v) = M * Matrix.gram ℝ v * Mᵀ := by
  ext i j
  simp only [Matrix.gram_apply, mixF, Matrix.mul_apply, Matrix.transpose_apply]
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma gdet_mixF {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → E) :
    gdet (mixF M v) = M.det ^ 2 * gdet v := by
  unfold gdet
  rw [gram_mixF, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

lemma gdet_pos {r : ℕ} {v : Fin r → E} (hv : LinearIndependent ℝ v) : 0 < gdet v :=
  (Matrix.posDef_gram_of_linearIndependent hv).det_pos

lemma linearIndependent_of_gdet_ne_zero {r : ℕ} {v : Fin r → E} (h : gdet v ≠ 0) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  apply h
  rw [gdet, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨g, fun he => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hne; exact hi (congrFun he i)
  · ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply, Pi.zero_apply]
    have : ∑ j, @inner ℝ E _ (v i) (v j) * g j = @inner ℝ E _ (v i) (∑ j, g j • v j) := by
      rw [inner_sum]; simp_rw [inner_smul_right]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hg, inner_zero_right]

/-- Orthogonal splitting of the Gram determinant. -/
lemma gdet_cons_orth {r : ℕ} (x : E) (w : Fin r → E) (h : ∀ j, @inner ℝ E _ x (w j) = 0) :
    gdet (Fin.cons x w : Fin (r + 1) → E) = ‖x‖ ^ 2 * gdet w := by
  unfold gdet
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin r, Matrix.gram ℝ (Fin.cons x w : Fin (r + 1) → E) i.succ 0 = 0 := by
    intro i
    simp only [Matrix.gram_apply, Fin.cons_succ, Fin.cons_zero]
    rw [real_inner_comm]; exact h i
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, pow_zero, one_mul,
    Fin.val_zero]
  congr 1
  simp [Matrix.gram_apply]

end

end GT
end File_GT_Lattice

section File_GT_Torus
/-!
# Tori and locally quadratic maps (Green–Tao §4, §5)

Green–Tao work with *dilated tori* `∏ ℝ/λ_i ℤ`.  Since the orthogonal complement of a dual
frequency in a dilated torus is not itself a dilated torus (their Theorem 5.1 handles this by a
bilipschitz reparametrisation), we instead work with the slightly more general class of tori
`ℝ^d / Γ`, where `Γ` is a lattice with a given basis, isometrically embedded in a Euclidean
space.  Concretely a torus `G` is given by vectors `v_1, …, v_d` of `ℝ^n`; its points are
`(ℝ/ℤ)^d`, the point with coordinates `t` corresponds to `∑ t_i v_i` modulo the lattice
`Γ = ⊕ ℤ v_i`, and the metric is the quotient Euclidean metric.  The volume is the covolume of
`Γ`, i.e. the square root of the Gram determinant of the `v_i`.  Dilated tori are the case of
orthogonal `v_i` with `‖v_i‖ = λ_i`.
-/

namespace GT

noncomputable section

open Finset

namespace DTorus

lemma vol_nonneg (G : DTorus) : 0 ≤ G.vol := Finset.prod_nonneg fun i _ => norm_nonneg _

end DTorus

end

end GT
end File_GT_Torus

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

/-- Cauchy–Schwarz eliminating a `1`-bounded factor. -/
lemma cs_elim2 {μ : α → ℝ} {ν : β → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (a b : α → β → ℝ) (ha : ∀ x y, |a x y| ≤ 1) :
    (∑ x, ∑ y, μ x * ν y * (a x y * b x y)) ^ 2 ≤ ∑ x, ∑ y, μ x * ν y * b x y ^ 2 := by
  have h0 : ∀ z : α × β, 0 ≤ μ z.1 * ν z.2 := fun z => mul_nonneg (hμ _) (hν _)
  have h1 : ∑ z : α × β, μ z.1 * ν z.2 = 1 := by
    rw [Fintype.sum_prod_type]; simp only [← mul_sum, hν1, mul_one, hμ1]
  have := sq_wavg_le (fun z : α × β => a z.1 z.2 * b z.1 z.2) h0 h1
  simp only [Fintype.sum_prod_type] at this
  refine this.trans (sum_le_sum fun x _ => sum_le_sum fun y _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (h0 (x, y))
  rw [mul_pow]
  have : a x y ^ 2 ≤ 1 := by
    have := ha x y; rw [← sq_abs]; nlinarith [abs_nonneg (a x y)]
  nlinarith [sq_nonneg (b x y)]

lemma prod_dist {μ : α → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) :
    (∀ z : α × α, 0 ≤ μ z.1 * μ z.2) ∧ ∑ z : α × α, μ z.1 * μ z.2 = 1 := by
  refine ⟨fun z => mul_nonneg (hμ _) (hμ _), ?_⟩
  rw [Fintype.sum_prod_type]; simp only [← mul_sum, hμ1, mul_one]

lemma sum4_perm {δ : Type*} [Fintype δ] (F : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ d, ∑ b, F a b c d := by
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm]; refine sum_congr rfl fun c _ => sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
        refine sum_congr rfl fun c _ => ?_
        rw [sum_comm]; refine sum_congr rfl fun d _ => sum_comm

lemma sum3_rev (F : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
        sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := sum_comm
    _ = ∑ c, ∑ b, ∑ a, F a b c := sum_congr rfl fun c _ => sum_comm

/-- Popularity: if a nonnegative bounded quantity has large mean, it is large with
noticeable probability. -/
lemma popular {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (X : α → ℝ)
    {B t c : ℝ} (ht : 0 ≤ t) (hXB : ∀ x, X x ≤ B) (h : c ≤ ∑ x, P x * X x) :
    c - t ≤ B * ∑ x, P x * (if t ≤ X x then 1 else 0) := by
  have : ∑ x, P x * X x ≤ ∑ x, P x * (B * (if t ≤ X x then 1 else 0) + t) := by
    refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hP x)
    split_ifs with hx
    · have := hXB x
      linarith
    · push_neg at hx; linarith
  have e : ∑ x, P x * (B * (if t ≤ X x then 1 else 0) + t) =
      B * ∑ x, P x * (if t ≤ X x then 1 else 0) + t := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hP1, one_mul, mul_sum]
    congr 1; exact sum_congr rfl fun x _ => by ring
  linarith

end cs

variable {p : ℕ} [NeZero p]

/-- The real `8`-point box average. -/
def box3 (P Q R : ZMod p → ℝ) (U : ZMod p → ℝ) : ℝ :=
  ∑ x, ∑ x', ∑ y, ∑ y', ∑ z, ∑ z', P x * P x' * Q y * Q y' * R z * R z' *
    (U (x + y + z) * U (x + y' + z) * U (x' + y + z) * U (x' + y' + z) * U (x + y + z') *
      U (x + y' + z') * U (x' + y + z') * U (x' + y' + z'))

lemma u3avg_ofReal (S : Finset (ZMod p)) (ρ0 ρ1 ρ2 : ℝ) (U : ZMod p → ℝ) :
    u3avg S ρ0 ρ1 ρ2 (fun x => (U x : ℂ)) =
      ((box3 (regP S ρ0) (regP S ρ1) (regP S ρ2) U : ℝ) : ℂ) := by
  unfold u3avg box3
  simp only [Complex.conj_ofReal]
  push_cast
  rfl

/-- **Triple Cauchy–Schwarz** (generalised von Neumann core). -/
theorem cs3 {P Q R : ZMod p → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (hQ : ∀ x, 0 ≤ Q x) (hQ1 : ∑ x, Q x = 1) (hR : ∀ x, 0 ≤ R x) (hR1 : ∑ x, R x = 1)
    (A B C : ZMod p → ZMod p → ℝ) (U : ZMod p → ℝ) (hA : ∀ y z, |A y z| ≤ 1)
    (hB : ∀ x z, |B x z| ≤ 1) (hC : ∀ x y, |C x y| ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ε ≤ |∑ x, ∑ y, ∑ z, P x * Q y * R z * (A y z * B x z * C x y * U (x + y + z))|) :
    ε ^ 8 ≤ box3 P Q R U := by
  obtain ⟨hPP, hPP1⟩ := prod_dist hP hP1
  obtain ⟨hQQ, hQQ1⟩ := prod_dist hQ hQ1
  set V : ZMod p → ZMod p → ℝ := fun y z => ∑ x, P x * (B x z * C x y * U (x + y + z)) with hV
  have e1 : ∑ x, ∑ y, ∑ z, P x * Q y * R z * (A y z * B x z * C x y * U (x + y + z)) =
      ∑ y, ∑ z, Q y * R z * (A y z * V y z) := by
    rw [sum_comm]; refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]; refine sum_congr rfl fun z _ => ?_
    rw [hV, mul_sum, mul_sum]; exact sum_congr rfl fun x _ => by ring
  have s1 : ε ^ 2 ≤ ∑ y, ∑ z, Q y * R z * V y z ^ 2 := by
    have := cs_elim2 hQ hQ1 hR hR1 A V hA
    rw [← e1] at this
    exact (pow_le_pow_left₀ hε h 2).trans ((sq_abs _).le.trans this)
  set W : ZMod p × ZMod p → ZMod p → ℝ := fun xx z => ∑ y, Q y * (C xx.1 y * C xx.2 y *
    (U (xx.1 + y + z) * U (xx.2 + y + z))) with hW
  have e2 : ∑ y, ∑ z, Q y * R z * V y z ^ 2 =
      ∑ xx : ZMod p × ZMod p, ∑ z, P xx.1 * P xx.2 * R z * ((B xx.1 z * B xx.2 z) * W xx z) := by
    rw [Fintype.sum_prod_type]
    simp only [hV, hW, sq, mul_sum, sum_mul]
    rw [sum4_perm, sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => sum_congr rfl fun z _ =>
      sum_congr rfl fun y _ => by ring
  have hBB : ∀ (xx : ZMod p × ZMod p) z, |B xx.1 z * B xx.2 z| ≤ 1 := fun xx z => by
    rw [abs_mul]; exact mul_le_one₀ (hB _ _) (abs_nonneg _) (hB _ _)
  have s2 : ε ^ 4 ≤ ∑ xx : ZMod p × ZMod p, ∑ z, P xx.1 * P xx.2 * R z * W xx z ^ 2 := by
    have := cs_elim2 (μ := fun xx : ZMod p × ZMod p => P xx.1 * P xx.2) hPP hPP1 hR hR1
      (fun xx z => B xx.1 z * B xx.2 z) W hBB
    rw [← e2] at this
    calc ε ^ 4 = (ε ^ 2) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) s1 2
      _ ≤ _ := this
  set Y : ZMod p × ZMod p → ZMod p × ZMod p → ℝ := fun xx yy => ∑ z, R z *
    (U (xx.1 + yy.1 + z) * U (xx.1 + yy.2 + z) * U (xx.2 + yy.1 + z) * U (xx.2 + yy.2 + z))
    with hY
  have e3 : ∑ xx : ZMod p × ZMod p, ∑ z, P xx.1 * P xx.2 * R z * W xx z ^ 2 =
      ∑ xx : ZMod p × ZMod p, ∑ yy : ZMod p × ZMod p, P xx.1 * P xx.2 * (Q yy.1 * Q yy.2) *
        ((C xx.1 yy.1 * C xx.2 yy.1 * C xx.1 yy.2 * C xx.2 yy.2) * Y xx yy) := by
    refine sum_congr rfl fun xx _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [hW, hY, sq, mul_sum, sum_mul]
    rw [sum3_rev]
    refine sum_congr rfl fun y _ => sum_congr rfl fun y' _ => sum_congr rfl fun z _ => by ring
  have hCC : ∀ (xx yy : ZMod p × ZMod p),
      |C xx.1 yy.1 * C xx.2 yy.1 * C xx.1 yy.2 * C xx.2 yy.2| ≤ 1 := fun xx yy => by
    simp only [abs_mul]
    refine mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (hC _ _) (abs_nonneg _) (hC _ _))
      (abs_nonneg _) (hC _ _)) (abs_nonneg _) (hC _ _)
  have s3 : ε ^ 8 ≤ ∑ xx : ZMod p × ZMod p, ∑ yy : ZMod p × ZMod p,
      P xx.1 * P xx.2 * (Q yy.1 * Q yy.2) * Y xx yy ^ 2 := by
    have := cs_elim2 (μ := fun xx : ZMod p × ZMod p => P xx.1 * P xx.2)
      (ν := fun yy : ZMod p × ZMod p => Q yy.1 * Q yy.2) hPP hPP1 hQQ hQQ1 _ Y hCC
    rw [← e3] at this
    calc ε ^ 8 = (ε ^ 4) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) s2 2
      _ ≤ _ := this
  refine s3.trans (le_of_eq ?_)
  unfold box3
  simp only [Fintype.sum_prod_type, hY, sq, mul_sum, sum_mul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => sum_congr rfl fun y _ =>
    sum_congr rfl fun y' _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun z _ => sum_congr rfl fun z' _ => by ring

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

section File_GT_VN
/-!
# The local generalised von Neumann theorem (Green–Tao, proof of Proposition 8.2)

If a four-term progression average `E Λ(H₀, H₁, H₂, H₃)` over `a ∈ n₀ + B(S, ρ_a)`,
`r ∈ B(S, ρ_r)` is large, then for many `a` the function `x ↦ H_i(a + 6x)` has a large local
`U³`-type box average at scales `ρ_A, θρ_A, θ²ρ_A`.  The proof: replace `a` by `a - i r`, then
`a` by `a + 6(n₁+n₂+n₃)` and `r` by `r + t_i(n)` so that every other slot misses one of the
`n_k`, fix `a` and `r`, and apply Cauchy–Schwarz three times.
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The four-term progression product. -/
def ap4 (H : Fin 4 → ZMod p → ℝ) (a r : ZMod p) : ℝ :=
  H 0 a * H 1 (a + r) * H 2 (a + 2 * r) * H 3 (a + 3 * r)

lemma abs_ap4_le {H : Fin 4 → ZMod p → ℝ} (hH : ∀ j x, |H j x| ≤ 1) (a r : ZMod p) :
    |ap4 H a r| ≤ 1 := by
  unfold ap4; simp only [abs_mul]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (hH _ _) (abs_nonneg _) (hH _ _))
    (abs_nonneg _) (hH _ _)) (abs_nonneg _) (hH _ _)

lemma ap4_eq {H : Fin 4 → ZMod p → ℝ} {x y a0 a1 a2 a3 : ZMod p} (h0 : x = a0)
    (h1 : x + y = a1) (h2 : x + 2 * y = a2) (h3 : x + 3 * y = a3) :
    ap4 H x y = H 0 a0 * H 1 a1 * H 2 a2 * H 3 a3 := by
  subst h0 h1 h2 h3; rfl

/-- The shift of `r` used for slot `i`. -/
def vnT (i : Fin 4) (n1 n2 n3 : ZMod p) : ZMod p :=
  match i with
  | 0 => -6 * n1 - 3 * n2 - 2 * n3
  | 1 => 6 * n1 - 6 * n2 - 3 * n3
  | 2 => 3 * n1 + 6 * n2 - 6 * n3
  | 3 => 2 * n1 + 3 * n2 + 6 * n3

lemma snorm_vnT (S : Finset (ZMod p)) (i : Fin 4) (n1 n2 n3 : ZMod p) :
    snorm S (vnT i n1 n2 n3) ≤ 6 * (snorm S n1 + snorm S n2 + snorm S n3) := by
  have h : ∀ (c1 c2 c3 : ℤ), |(c1 : ℝ)| ≤ 6 → |(c2 : ℝ)| ≤ 6 → |(c3 : ℝ)| ≤ 6 →
      snorm S ((c1 : ZMod p) * n1 + (c2 : ZMod p) * n2 + (c3 : ZMod p) * n3) ≤
        6 * (snorm S n1 + snorm S n2 + snorm S n3) := by
    intro c1 c2 c3 h1 h2 h3
    have a1 := snorm_intsmul_le (S := S) c1 n1
    have a2 := snorm_intsmul_le (S := S) c2 n2
    have a3 := snorm_intsmul_le (S := S) c3 n3
    have b1 := snorm_nonneg (S := S) n1
    have b2 := snorm_nonneg (S := S) n2
    have b3 := snorm_nonneg (S := S) n3
    refine (snorm_add_le _ _).trans ?_
    have := snorm_add_le (S := S) ((c1 : ZMod p) * n1) ((c2 : ZMod p) * n2)
    nlinarith [mul_le_mul_of_nonneg_right h1 b1, mul_le_mul_of_nonneg_right h2 b2,
      mul_le_mul_of_nonneg_right h3 b3]
  fin_cases i
  · have := h (-6) (-3) (-2) (by norm_num) (by norm_num) (by norm_num)
    simp only [vnT]; push_cast at this; convert this using 2 <;> ring
  · have := h 6 (-6) (-3) (by norm_num) (by norm_num) (by norm_num)
    simp only [vnT]; push_cast at this; convert this using 2 <;> ring
  · have := h 3 6 (-6) (by norm_num) (by norm_num) (by norm_num)
    simp only [vnT]; push_cast at this; convert this using 2 <;> ring
  · have := h 2 3 6 (by norm_num) (by norm_num) (by norm_num)
    simp only [vnT]; push_cast at this; convert this using 2 <;> ring

/-- After the change of variables every slot other than `i` misses one of the `n_k`. -/
lemma vn_factor (H : Fin 4 → ZMod p → ℝ) (hH : ∀ j x, |H j x| ≤ 1) (i : Fin 4) (a r : ZMod p) :
    ∃ A B C : ZMod p → ZMod p → ℝ, (∀ y z, |A y z| ≤ 1) ∧ (∀ x z, |B x z| ≤ 1) ∧
      (∀ x y, |C x y| ≤ 1) ∧ ∀ n1 n2 n3 : ZMod p,
        ap4 H (a + 6 * (n1 + n2 + n3) - (i.val : ZMod p) * (r + vnT i n1 n2 n3))
          (r + vnT i n1 n2 n3) =
        A n2 n3 * B n1 n3 * C n1 n2 * H i (a + 6 * (n1 + n2 + n3)) := by
  fin_cases i
  · refine ⟨fun y z => H 1 (a + r + 3 * y + 4 * z), fun x z => H 2 (a + 2 * r - 6 * x + 2 * z),
      fun x y => H 3 (a + 3 * r - 12 * x - 3 * y), fun _ _ => hH _ _, fun _ _ => hH _ _,
      fun _ _ => hH _ _, fun n1 n2 n3 => ?_⟩
    simp only [vnT]
    rw [ap4_eq (a0 := a + 6 * (n1 + n2 + n3)) (a1 := a + r + 3 * n2 + 4 * n3)
      (a2 := a + 2 * r - 6 * n1 + 2 * n3) (a3 := a + 3 * r - 12 * n1 - 3 * n2)]
    all_goals
      first
      | (simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue]; done)
      | (simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue]; ring)
      | ring
      | (simp; ring)
      | simp
  · refine ⟨fun y z => H 0 (a - r + 12 * y + 9 * z), fun x z => H 2 (a + r + 12 * x + 3 * z),
      fun x y => H 3 (a + 2 * r + 18 * x - 6 * y), fun _ _ => hH _ _, fun _ _ => hH _ _,
      fun _ _ => hH _ _, fun n1 n2 n3 => ?_⟩
    simp only [vnT]
    rw [ap4_eq (a0 := a - r + 12 * n2 + 9 * n3) (a1 := a + 6 * (n1 + n2 + n3))
      (a2 := a + r + 12 * n1 + 3 * n3) (a3 := a + 2 * r + 18 * n1 - 6 * n2)]
    all_goals
      first
      | (simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue]; done)
      | (simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue]; ring)
      | ring
      | (simp; ring)
      | simp
  · refine ⟨fun y z => H 0 (a - 2 * r - 6 * y + 18 * z), fun x z => H 1 (a - r + 3 * x + 12 * z),
      fun x y => H 3 (a + r + 9 * x + 12 * y), fun _ _ => hH _ _, fun _ _ => hH _ _,
      fun _ _ => hH _ _, fun n1 n2 n3 => ?_⟩
    simp only [vnT]
    rw [ap4_eq (a0 := a - 2 * r - 6 * n2 + 18 * n3) (a1 := a - r + 3 * n1 + 12 * n3)
      (a2 := a + 6 * (n1 + n2 + n3)) (a3 := a + r + 9 * n1 + 12 * n2)]
    all_goals
      first
      | (simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue]; done)
      | (simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue]; ring)
      | ring
      | (simp; ring)
      | simp
  · refine ⟨fun y z => H 0 (a - 3 * r - 3 * y - 12 * z), fun x z => H 1 (a - 2 * r + 2 * x - 6 * z),
      fun x y => H 2 (a - r + 4 * x + 3 * y), fun _ _ => hH _ _, fun _ _ => hH _ _,
      fun _ _ => hH _ _, fun n1 n2 n3 => ?_⟩
    simp only [vnT]
    rw [ap4_eq (a0 := a - 3 * r - 3 * n2 - 12 * n3) (a1 := a - 2 * r + 2 * n1 - 6 * n3)
      (a2 := a - r + 4 * n1 + 3 * n2) (a3 := a + 6 * (n1 + n2 + n3))]
    all_goals
      first
      | (simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue]; done)
      | (simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue]; ring)
      | ring
      | (simp; ring)
      | simp

end

end GT

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma sum3_regP_sub {S : Finset (ZMod p)} {ρ1 ρ2 ρ3 : ℝ} (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2)
    (h3 : 0 ≤ ρ3) (c : ℝ) :
    ∑ n1, ∑ n2, ∑ n3, regP S ρ1 n1 * regP S ρ2 n2 * regP S ρ3 n3 * c = c := by
  have e3 : ∀ n1 n2, ∑ n3, regP S ρ1 n1 * regP S ρ2 n2 * regP S ρ3 n3 * c =
      regP S ρ1 n1 * c * regP S ρ2 n2 := fun n1 n2 => by
    rw [← sum_mul, ← mul_sum, sum_regP _ h3]; ring
  simp only [e3, ← mul_sum, sum_regP _ h2, mul_one, ← sum_mul, sum_regP _ h1, one_mul]

lemma sum5_perm {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] (F : α → β → γ → δ → ε → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e = ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, F a b c d e := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e = ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, F a b c d e :=
        sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, ∑ e, F a b c d e := sum_congr rfl fun a _ => sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, ∑ e, F a b c d e := sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ e, ∑ c, F a b c d e :=
        sum_congr rfl fun d _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_comm
    _ = ∑ d, ∑ a, ∑ e, ∑ b, ∑ c, F a b c d e :=
        sum_congr rfl fun d _ => sum_congr rfl fun a _ => sum_comm
    _ = ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, F a b c d e := sum_congr rfl fun d _ => sum_comm

/-- **Local generalised von Neumann theorem.** -/
theorem vn_core {S : Finset (ZMod p)} {n0 : ZMod p} {ρa ρr ρA θ δ : ℝ}
    (hρa : 0 < ρa) (hρr : 0 < ρr) (hρA : 0 < ρA) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ)
    (i : Fin 4) (H : Fin 4 → ZMod p → ℝ) (hH : ∀ j x, |H j x| ≤ 1)
    (h : δ ≤ |∑ a, ∑ r, regP S ρa (a - n0) * regP S ρr r * ap4 H a r|)
    (h1 : 12 * ρr ≤ ρa) (h1' : 50 * S.card * (3 * ρr) / ρa ≤ δ / 8)
    (h2 : 72 * ρA ≤ ρa) (h2' : 50 * S.card * (18 * ρA) / ρa ≤ δ / 16)
    (h3 : 72 * ρA ≤ ρr) (h3' : 50 * S.card * (18 * ρA) / ρr ≤ δ / 16) :
    δ / 4 ≤ ∑ a, regP S ρa (a - n0) *
      (if (δ / 4) ^ 8 ≤ box3 (regP S ρA) (regP S (θ * ρA)) (regP S (θ ^ 2 * ρA))
        (fun x => H i (a + 6 * x)) then 1 else 0) := by
  set Pa : ZMod p → ℝ := fun a => regP S ρa (a - n0) with hPa
  have hPa0 : ∀ a, 0 ≤ Pa a := fun a => regP_nonneg _ _
  have hPa1 : ∑ a, Pa a = 1 := by
    rw [hPa]; simp only; rw [sum_sub_right (regP S ρa) n0]; exact sum_regP _ hρa.le
  have hPr := regP_isDist S hρr.le
  have hθρ : 0 < θ * ρA := mul_pos hθ0 hρA
  have hθ2ρ : 0 < θ ^ 2 * ρA := by positivity
  set Φ1 : ZMod p → ZMod p → ℝ := fun a r => ap4 H (a - (i.val : ZMod p) * r) r with hΦ1
  have hΦ1b : ∀ a r, |Φ1 a r| ≤ 1 := fun a r => abs_ap4_le hH _ _
  set I0 := ∑ a, ∑ r, Pa a * regP S ρr r * ap4 H a r with hI0
  set I1 := ∑ a, ∑ r, Pa a * regP S ρr r * Φ1 a r with hI1
  -- step 1
  have hi3 : (i.val : ℝ) ≤ 3 := by have := i.isLt; exact_mod_cast Nat.le_of_lt_succ this
  have s1 : |I1 - I0| ≤ δ / 8 := by
    have e : I1 - I0 = ∑ r, regP S ρr r * (∑ a, Pa a * Φ1 a r - ∑ a, Pa a * ap4 H a r) := by
      rw [hI1, hI0, sum_comm, sum_comm (f := fun a r => Pa a * regP S ρr r * ap4 H a r),
        ← sum_sub_distrib]
      refine sum_congr rfl fun r _ => ?_
      rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [e]
    refine (abs_wavg_le hPr.1 hPr.2 _ (fun r hr => ?_)).trans (le_refl _) |>.trans h1'
    have hrb : snorm S r ≤ ρr := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρr.le hr) hρr.le
    have hsn : snorm S (-((i.val : ZMod p) * r)) ≤ 3 * ρr := by
      rw [snorm_neg]
      refine (snorm_nsmul_le _ _).trans ?_
      exact mul_le_mul hi3 hrb (snorm_nonneg _) (by norm_num)
    have := shift_real_c subset_rfl hρa (by linarith) hsn n0 (fun a => ap4 H a r)
      (B := 1) (fun a => abs_ap4_le hH _ _)
    simpa [hPa, hΦ1, sub_eq_add_neg] using this
  -- step 2
  set J : ZMod p → ZMod p → ZMod p → ℝ := fun n1 n2 n3 => ∑ a, ∑ r, Pa a * regP S ρr r *
    Φ1 (a + 6 * (n1 + n2 + n3)) (r + vnT i n1 n2 n3) with hJ
  set I2 := ∑ n1, ∑ n2, ∑ n3, regP S ρA n1 * regP S (θ * ρA) n2 * regP S (θ ^ 2 * ρA) n3 *
    J n1 n2 n3 with hI2
  have s2 : |I2 - I1| ≤ δ / 8 := by
    have e : I2 - I1 = ∑ n1, ∑ n2, ∑ n3, regP S ρA n1 * regP S (θ * ρA) n2 *
        regP S (θ ^ 2 * ρA) n3 * (J n1 n2 n3 - I1) := by
      rw [hI2]
      conv_lhs => rw [← sum3_regP_sub (p := p) (S := S) hρA.le hθρ.le hθ2ρ.le I1]
      simp only [← sum_sub_distrib, mul_sub]
    rw [e]
    have hμ : ∀ z : ZMod p × ZMod p × ZMod p,
        0 ≤ regP S ρA z.1 * regP S (θ * ρA) z.2.1 * regP S (θ ^ 2 * ρA) z.2.2 :=
      fun z => mul_nonneg (mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)) (regP_nonneg _ _)
    have hμ1 : ∑ z : ZMod p × ZMod p × ZMod p,
        regP S ρA z.1 * regP S (θ * ρA) z.2.1 * regP S (θ ^ 2 * ρA) z.2.2 = 1 := by
      simp only [Fintype.sum_prod_type]
      have := sum3_regP_sub (p := p) (S := S) (ρ1 := ρA) (ρ2 := θ * ρA) (ρ3 := θ ^ 2 * ρA)
        hρA.le hθρ.le hθ2ρ.le 1
      simpa only [mul_one] using this
    have := abs_wavg_le hμ hμ1 (fun z => J z.1 z.2.1 z.2.2 - I1) (B := δ / 8) (fun z hz => ?_)
    · simpa [Fintype.sum_prod_type] using this
    have hz1 : regP S ρA z.1 ≠ 0 := fun h0 => hz (by simp [h0])
    have hz2 : regP S (θ * ρA) z.2.1 ≠ 0 := fun h0 => hz (by simp [h0])
    have hz3 : regP S (θ ^ 2 * ρA) z.2.2 ≠ 0 := fun h0 => hz (by simp [h0])
    have b1 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρA.le hz1) hρA.le
    have b2 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hθρ.le hz2) hθρ.le
    have b3 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hθ2ρ.le hz3) hθ2ρ.le
    have hθρ' : θ * ρA ≤ ρA := by nlinarith
    have hθ2ρ' : θ ^ 2 * ρA ≤ ρA := by nlinarith [pow_le_one₀ hθ0.le hθ1 (n := 2)]
    have hsum : snorm S z.1 + snorm S z.2.1 + snorm S z.2.2 ≤ 3 * ρA := by linarith
    have hs : snorm S (6 * (z.1 + z.2.1 + z.2.2)) ≤ 18 * ρA := by
      have := snorm_nsmul_le (S := S) 6 (z.1 + z.2.1 + z.2.2)
      have h' := snorm_add_le (S := S) (z.1 + z.2.1) z.2.2
      have h'' := snorm_add_le (S := S) z.1 z.2.1
      push_cast at this; linarith
    have ht : snorm S (vnT i z.1 z.2.1 z.2.2) ≤ 18 * ρA := by
      have := snorm_vnT S i z.1 z.2.1 z.2.2; linarith
    have := shift_pair hρa hρr (by linarith) (by linarith) hs ht n0 Φ1 hΦ1b
    calc |J z.1 z.2.1 z.2.2 - I1| ≤ _ := by simpa [hJ, hI1, hPa] using this
      _ ≤ δ / 16 + δ / 16 := add_le_add h2' h3'
      _ = δ / 8 := by ring
  have hI2b : 5 * δ / 8 ≤ |I2| := by
    have := abs_sub_abs_le_abs_sub I0 I2
    have := abs_sub_le I0 I1 I2
    rw [abs_sub_comm] at s1 s2
    linarith
  -- rearrange
  set Y : ZMod p → ZMod p → ℝ := fun a r => ∑ n1, ∑ n2, ∑ n3, regP S ρA n1 *
    regP S (θ * ρA) n2 * regP S (θ ^ 2 * ρA) n3 *
      Φ1 (a + 6 * (n1 + n2 + n3)) (r + vnT i n1 n2 n3) with hY
  set X : ZMod p → ℝ := fun a => ∑ r, regP S ρr r * Y a r with hX
  have eI2 : I2 = ∑ a, Pa a * X a := by
    rw [hI2]; simp only [hJ, hX, hY, mul_sum]
    rw [sum5_perm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun r _ => sum_congr rfl fun n1 _ =>
      sum_congr rfl fun n2 _ => sum_congr rfl fun n3 _ => by ring
  have hw : ∀ z : ZMod p × ZMod p × ZMod p,
      0 ≤ regP S ρA z.1 * regP S (θ * ρA) z.2.1 * regP S (θ ^ 2 * ρA) z.2.2 :=
    fun z => mul_nonneg (mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)) (regP_nonneg _ _)
  have hw1 : ∑ z : ZMod p × ZMod p × ZMod p,
      regP S ρA z.1 * regP S (θ * ρA) z.2.1 * regP S (θ ^ 2 * ρA) z.2.2 = 1 := by
    simp only [Fintype.sum_prod_type]
    have := sum3_regP_sub (p := p) (S := S) (ρ1 := ρA) (ρ2 := θ * ρA) (ρ3 := θ ^ 2 * ρA)
      hρA.le hθρ.le hθ2ρ.le 1
    simpa only [mul_one] using this
  have hYb : ∀ a r, |Y a r| ≤ 1 := fun a r => by
    have := abs_wavg_le hw hw1 (fun z => Φ1 (a + 6 * (z.1 + z.2.1 + z.2.2))
      (r + vnT i z.1 z.2.1 z.2.2)) (B := 1) (fun z _ => hΦ1b _ _)
    simpa [hY, Fintype.sum_prod_type] using this
  have hXb : ∀ a, |X a| ≤ 1 := fun a => abs_wavg_le hPr.1 hPr.2 _ (fun r _ => hYb a r)
  have hmean : 5 * δ / 8 ≤ ∑ a, Pa a * |X a| := by
    refine hI2b.trans ?_
    rw [eI2]; refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact sum_congr rfl fun a _ => by rw [abs_mul, abs_of_nonneg (hPa0 a)]
  have hpop := popular hPa0 hPa1 (fun a => |X a|) (B := 1) (t := δ / 4) (by linarith)
    (fun a => hXb a) hmean
  have hgood : ∀ a, δ / 4 ≤ |X a| → (δ / 4) ^ 8 ≤ box3 (regP S ρA) (regP S (θ * ρA))
      (regP S (θ ^ 2 * ρA)) (fun x => H i (a + 6 * x)) := by
    intro a ha
    have ha' : δ / 4 ≤ ∑ r, regP S ρr r * |Y a r| := by
      refine ha.trans ((abs_sum_le_sum_abs _ _).trans (le_of_eq ?_))
      exact sum_congr rfl fun r _ => by rw [abs_mul, abs_of_nonneg (regP_nonneg _ _)]
    obtain ⟨r, -, hr⟩ := exists_pos_ge hPr.1 hPr.2 _ ha'
    obtain ⟨A, B, C, hA, hB, hC, hfac⟩ := vn_factor H hH i a r
    have hP := regP_isDist S hρA.le
    have hQ := regP_isDist S hθρ.le
    have hR := regP_isDist S hθ2ρ.le
    refine cs3 hP.1 hP.2 hQ.1 hQ.2 hR.1 hR.2 A B C (fun x => H i (a + 6 * x)) hA hB hC
      (by linarith) (hr.trans (le_of_eq ?_))
    congr 1
    simp only [hY, hΦ1]
    refine sum_congr rfl fun n1 _ => sum_congr rfl fun n2 _ => sum_congr rfl fun n3 _ => ?_
    rw [hfac]
  have hmono : ∑ a, Pa a * (if δ / 4 ≤ |X a| then 1 else 0) ≤ ∑ a, regP S ρa (a - n0) *
      (if (δ / 4) ^ 8 ≤ box3 (regP S ρA) (regP S (θ * ρA)) (regP S (θ ^ 2 * ρA))
        (fun x => H i (a + 6 * x)) then 1 else 0) := by
    refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hPa0 a)
    by_cases ha : δ / 4 ≤ |X a|
    · rw [if_pos ha, if_pos (hgood a ha)]
    · rw [if_neg ha]; split_ifs <;> norm_num
  linarith

end

end GT
end File_GT_VN

section File_GT_Iter
/-!
# The energy/dimension iteration (Green–Tao, end of §3)

A *random triple* `(a, r, 𝐟)` in which `𝐟` becomes deterministic after conditioning on a
finite label `c` is encoded by `Triple p`: a finite label type with a probability vector `π`,
for each label a joint law `w c` of `(a, r)`, and a function `F c`.

`MainAbstract C₂ C₅` is Proposition 3.3 of Green–Tao (with the path-length bound `64 η^{-2C₂}`
and the thickness bound `exp(η^{-C₅})/p`), and `khint_of_mainAbstract` deduces Theorem 3.1.
-/

open Finset

namespace GT

noncomputable section

namespace Triple

variable {p : ℕ} [NeZero p] (t : Triple p) (f : ZMod p → ℝ)

/-- Validity: probability vectors, and `𝐟` is `1`-bounded. -/
def Valid : Prop :=
  (∀ c, 0 ≤ t.π c) ∧ ∑ c, t.π c = 1 ∧ (∀ c z, 0 ≤ t.w c z) ∧ (∀ c, ∑ z, t.w c z = 1) ∧
    ∀ c x, |t.F c x| ≤ 1

end Triple

namespace Triple

variable {p : ℕ} [NeZero p] {t : Triple p} {f : ZMod p → ℝ}

end Triple

end

end GT
end File_GT_Iter

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

/-- `E g(a)` as an average of label averages. -/
lemma ex_eq (v : SLA p) (η : ℝ) (hη : 0 ≤ eps4 η) (hρ : ∀ c, 0 ≤ v.ρ c) (g : ZMod p → ℝ) :
    (v.triple η).ex g = ∑ c, v.prob c * (v.ldata c).avg g := by
  unfold Triple.ex LData.avg
  refine sum_congr rfl fun c _ => ?_
  congr 1
  simp only [triple, ldata]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  simp_rw [mul_assoc, ← mul_sum]
  congr 1
  rw [← sum_mul, sum_regP _ (mul_nonneg hη (hρ c)), one_mul]

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

variable (v : SLA p) (η : ℝ)

variable {v η}

/-! ### Statistics of the refined approximant -/

lemma avg_shift (L : LData p) (g : ZMod p → ℝ) :
    L.avg g = ∑ y, regP L.S (L.ρ / 2) y * g (L.n + y) := by
  unfold LData.avg
  exact (Fintype.sum_equiv (Equiv.addLeft L.n) _ _ fun y => by simp).symm

/-! ### Structural statistics -/

lemma nonempty_C (hv : v.Valid) : Nonempty v.C := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hv.2.1
  rw [Finset.univ_eq_empty, sum_empty] at this
  exact zero_ne_one this

end SLA

end

end GT
end File_GT_BadDim

section File_GT_BadEdA
/-!
# Theorem 6.6, the linear case: shifting the approximant by a constant

If `|E 𝐟(a) - E f(a)| > η`, adding the constant `±η/2` to every `F_c` (and truncating to
`[-1, 1]`) decreases the energy by at least `η²/2`, without changing any of the other data.
-/

open Finset KM

namespace GT

noncomputable section

/-- Truncation to `[-1, 1]`. -/
def clamp1 (x : ℝ) : ℝ := max (-1) (min 1 x)

lemma abs_clamp1_le (x : ℝ) : |clamp1 x| ≤ 1 := by
  unfold clamp1; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma abs_clamp1_sub_le (x y : ℝ) : |clamp1 x - clamp1 y| ≤ |x - y| := by
  unfold clamp1
  have h1 := abs_max_sub_max_le_abs (min 1 x) (min 1 y) (-1)
  have h2 := abs_min_sub_min_le_max 1 x 1 y
  rw [max_comm (-1 : ℝ), max_comm (-1 : ℝ)]
  refine h1.trans (h2.trans ?_)
  simp

lemma clamp1_of_abs_le {a : ℝ} (ha : |a| ≤ 1) : clamp1 a = a := by
  obtain ⟨h1, h2⟩ := abs_le.1 ha
  unfold clamp1; rw [min_eq_right h2, max_eq_right h1]

lemma abs_sub_clamp1_le {a : ℝ} (ha : |a| ≤ 1) (x : ℝ) : |a - clamp1 x| ≤ |a - x| := by
  have := abs_clamp1_sub_le a x
  rwa [clamp1_of_abs_le ha] at this

lemma sq_sub_clamp1_le {a : ℝ} (ha : |a| ≤ 1) (x : ℝ) : (a - clamp1 x) ^ 2 ≤ (a - x) ^ 2 := by
  have := abs_sub_clamp1_le ha x
  rw [← sq_abs, ← sq_abs (a - x)]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

namespace SLA

variable {p : ℕ} [NeZero p]

/-- The triple of a valid approximant is valid. -/
lemma triple_valid {v : SLA p} (hv : v.Valid) (η : ℝ) : (v.triple η).Valid := by
  obtain ⟨h1, h2, -, h4, -, h6, -, -⟩ := hv
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro c z
    exact mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)
  · intro c
    change ∑ z : ZMod p × ZMod p, regP (v.S c) (v.ρ c / 2) (z.1 - v.n c) *
      regP (v.S c) (eps4 η * v.ρ c) z.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [sum_regP _ (by unfold eps4; have := (h4 c).1; positivity), ← Finset.sum_mul, mul_one,
      sum_sub_right (regP (v.S c) (v.ρ c / 2)) (v.n c), sum_regP _ (by linarith [(h4 c).1])]
  · intro c x
    exact h6 c _

lemma rmin_nonneg {v : SLA p} (hv : v.Valid) : 0 ≤ v.rmin :=
  Real.iInf_nonneg fun c => (hv.2.2.2.1 c).1.le

lemma volm_nonneg (v : SLA p) : 0 ≤ v.volm :=
  Real.iSup_nonneg fun c => (v.G c).vol_nonneg

/-- Shifting all the `F_c` by a constant `δ` (and truncating). -/
def shiftF (v : SLA p) (δ : ℝ) : SLA p :=
  { v with F := fun c y => clamp1 (v.F c y + δ) }

variable {v : SLA p} {δ η : ℝ} {f : ZMod p → ℝ}

lemma shiftF_valid (hv : v.Valid) : (v.shiftF δ).Valid := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  refine ⟨h1, h2, h3, h4, fun c t t' => ?_, fun c x => abs_clamp1_le _, h7, h8⟩
  refine (abs_clamp1_sub_le _ _).trans ?_
  rw [add_sub_add_right_eq_sub]
  exact h5 c t t'

lemma shiftF_edge (hv : v.Valid) (hη : 0 < η) : v.Edge η f (v.shiftF δ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (v.d1 : ℝ) ≤ v.d1 + (1 / η) ^ C2
    have : (0 : ℝ) ≤ (1 / η) ^ C2 := by positivity
    linarith
  · change v.d2 ≤ v.d2 + 1; omega
  · change Real.exp (-(1 / η) ^ C5) * v.rmin ≤ v.rmin
    have h0 := rmin_nonneg hv
    have : Real.exp (-(1 / η) ^ C5) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : (0 : ℝ) ≤ (1 / η) ^ C5 := by positivity
      linarith)
    nlinarith
  · change v.volm ≤ Real.exp ((1 / η) ^ C3) * v.volm
    have h0 := volm_nonneg v
    have : 1 ≤ Real.exp ((1 / η) ^ C3) := Real.one_le_exp (by positivity)
    nlinarith
  · have : v.waste η f = (v.shiftF δ).waste η f := rfl
    rw [this, sub_self, abs_zero]; positivity

lemma shiftF_energy (hv : v.Valid) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ((v.shiftF δ).triple η).energy f ≤
      (v.triple η).energy f - 2 * δ * ((v.triple η).ex f - (v.triple η).exF) + δ ^ 2 := by
  have ht := triple_valid hv η
  obtain ⟨hπ0, hπ1, hw0, hw1, -⟩ := ht
  have key : ∀ c z, (v.triple η).w c z * (f z.1 - clamp1 ((v.triple η).F c z.1 + δ)) ^ 2 ≤
      (v.triple η).w c z * ((f z.1 - (v.triple η).F c z.1) ^ 2 -
        2 * δ * (f z.1 - (v.triple η).F c z.1) + δ ^ 2) := by
    intro c z
    refine mul_le_mul_of_nonneg_left ?_ (hw0 c z)
    have hfz : |f z.1| ≤ 1 := abs_le.2 ⟨by linarith [(hf z.1).1], (hf z.1).2⟩
    refine (sq_sub_clamp1_le hfz _).trans (le_of_eq ?_)
    ring
  have e1 : ((v.shiftF δ).triple η).energy f = ∑ c, v.prob c * ∑ z, (v.triple η).w c z *
      (f z.1 - clamp1 ((v.triple η).F c z.1 + δ)) ^ 2 := rfl
  rw [e1]
  calc ∑ c, v.prob c * ∑ z, (v.triple η).w c z * (f z.1 - clamp1 ((v.triple η).F c z.1 + δ)) ^ 2
      ≤ ∑ c, v.prob c * ∑ z, (v.triple η).w c z * ((f z.1 - (v.triple η).F c z.1) ^ 2 -
        2 * δ * (f z.1 - (v.triple η).F c z.1) + δ ^ 2) :=
        sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => key c z) (hπ0 c)
    _ = (v.triple η).energy f - 2 * δ * ((v.triple η).ex f - (v.triple η).exF) + δ ^ 2 := by
        unfold Triple.energy Triple.ex Triple.exF
        have hw : ∀ c, ∑ z, (v.triple η).w c z = 1 := hw1
        have hπ : ∑ c, (v.triple η).π c = 1 := hπ1
        have e2 : ∀ c, ∑ z, (v.triple η).w c z * ((f z.1 - (v.triple η).F c z.1) ^ 2 -
            2 * δ * (f z.1 - (v.triple η).F c z.1) + δ ^ 2) =
            ∑ z, (v.triple η).w c z * (f z.1 - (v.triple η).F c z.1) ^ 2 -
            2 * δ * (∑ z, (v.triple η).w c z * f z.1 - ∑ z, (v.triple η).w c z *
              (v.triple η).F c z.1) + δ ^ 2 := by
          intro c
          simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_sum]
          rw [← sum_mul, hw c, one_mul]
          congr 1; congr 1
          congr 1 <;> exact sum_congr rfl fun _ _ => by ring
        change ∑ c, (v.triple η).π c * _ = ∑ c, (v.triple η).π c * _ - 2 * δ *
          (∑ c, (v.triple η).π c * _ - ∑ c, (v.triple η).π c * _) + δ ^ 2
        simp only [e2]
        simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_sum]
        rw [← sum_mul, hπ, one_mul]
        congr 1; congr 1
        congr 1 <;> exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- **Theorem 6.6, first case.** -/
theorem bad_ed_lin (hv : v.Valid) (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hbad : η < |(v.triple η).exF - (v.triple η).ex f|) :
    ∃ v' : SLA p, v'.Valid ∧ v.Edge η f v' ∧
      (v'.triple η).energy f ≤ (v.triple η).energy f - η ^ C2 := by
  set D := (v.triple η).ex f - (v.triple η).exF with hD
  have hD' : η < |D| := by rw [hD, abs_sub_comm]; exact hbad
  set δ := if 0 ≤ D then η / 2 else -(η / 2) with hδ
  have hδD : η / 2 * |D| = δ * D := by
    rw [hδ]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have hδ2 : δ ^ 2 = η ^ 2 / 4 := by rw [hδ]; split_ifs <;> ring
  refine ⟨v.shiftF δ, shiftF_valid hv, shiftF_edge hv hη0, ?_⟩
  refine (shiftF_energy hv hf).trans ?_
  rw [← hD, hδ2]
  have hC : η ^ C2 ≤ η ^ 2 / 2 := by
    have h2 : η ^ C2 ≤ η ^ 3 := pow_le_pow_of_le_one hη0.le (by linarith)
      (by unfold C2; norm_num)
    nlinarith [pow_pos hη0 2]
  nlinarith [mul_pos hη0 hη0]

end SLA

end

end GT
end File_GT_BadEdA

section File_GT_TorusExt
/-!
# Adjoining a circle factor to a torus

For the energy decrement of Theorem 6.6 the torus `G` is replaced by `G × (ℝ/ℤ)`, realised as
the lattice with basis `(0, 16)` and `(2 v_i, 0)`; the new function is
`F'(y, x) = clamp(F(x) + ε cos(2π y))`.
-/

open Finset KM

namespace GT

noncomputable section

/-- The embedding `ℝ^n → ℝ^{n+1}`, `x ↦ (0, x)`. -/
def ιE {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))

lemma inner_ιE {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (ιE x) (ιE y) = inner ℝ x y := by
  simp [ιE, PiLp.inner_apply, Fin.sum_univ_succ]

lemma inner_single_ιE {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (EuclideanSpace.single (0 : Fin (n + 1)) c) (ιE x) = 0 := by
  simp [ιE, PiLp.inner_apply, EuclideanSpace.single_apply]

lemma inner_ιE_single {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (ιE x) (EuclideanSpace.single (0 : Fin (n + 1)) c) = 0 := by
  rw [real_inner_comm]; exact inner_single_ιE c x

lemma ιE_add {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : ιE (x + y) = ιE x + ιE y := by
  ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [ιE]

lemma ιE_smul {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ιE (c • x) = c • ιE x := by
  ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [ιE]

lemma ιE_sum {n : ℕ} {κ : Type*} (s : Finset κ) (x : κ → EuclideanSpace ℝ (Fin n)) :
    ιE (∑ i ∈ s, x i) = ∑ i ∈ s, ιE (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [ιE]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, ιE_add, ih]

lemma norm_ιE {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖ιE x‖ = ‖x‖ := by
  have h := inner_ιE x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have := norm_nonneg (ιE x); have := norm_nonneg x
  nlinarith

namespace DTorus

/-- The torus `G × (ℝ/ℤ)` with lattice basis `(0, 16), (2 v_i, 0)`. -/
abbrev ext (G : DTorus) : DTorus where
  d := G.d + 1
  n := G.n + 1
  v := Fin.cons (EuclideanSpace.single 0 16) (fun i => (2 : ℝ) • ιE (G.v i))

variable (G : DTorus)

lemma ext_emb (t : Fin (G.d + 1) → ℝ) :
    G.ext.emb t = t 0 • EuclideanSpace.single (0 : Fin (G.n + 1)) (16 : ℝ) +
      (2 : ℝ) • ιE (G.emb (Fin.tail t)) := by
  change ∑ i, t i • (Fin.cons (EuclideanSpace.single 0 16) (fun i => (2 : ℝ) • ιE (G.v i)) :
    Fin (G.d + 1) → EuclideanSpace ℝ (Fin (G.n + 1))) i = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  rw [emb, ιE_sum, smul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [ιE_smul, smul_comm]
  rfl

lemma norm_ext_emb_sq (t : Fin (G.d + 1) → ℝ) :
    ‖G.ext.emb t‖ ^ 2 = 256 * t 0 ^ 2 + 4 * ‖G.emb (Fin.tail t)‖ ^ 2 := by
  rw [ext_emb, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  simp only [inner_ιE_single, inner_single_ιE,
    real_inner_self_eq_norm_sq, EuclideanSpace.norm_single, norm_ιE]
  norm_num; ring

lemma gram_ext_tail (w : Fin G.d → EuclideanSpace ℝ (Fin G.n)) :
    gdet (fun i => (2 : ℝ) • ιE (w i)) = 4 ^ G.d * gdet w := by
  have e : (fun i => (2 : ℝ) • ιE (w i)) = mixF ((2 : ℝ) • (1 : Matrix (Fin G.d) (Fin G.d) ℝ))
      (fun i => ιE (w i)) := by
    funext i
    simp only [mixF, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_smul, zero_smul, sum_ite_eq, mem_univ, if_true]
  rw [e, gdet_mixF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have : gdet (fun i => ιE (w i)) = gdet w := by
    unfold gdet; congr 1; ext i j; simp only [Matrix.gram_apply, inner_ιE]
  rw [this, ← pow_mul, mul_comm G.d 2, pow_mul]; norm_num

lemma gdet_ext : gdet G.ext.v = 256 * 4 ^ G.d * gdet G.v := by
  change gdet (Fin.cons (EuclideanSpace.single 0 16) (fun i => (2 : ℝ) • ιE (G.v i)) :
    Fin (G.d + 1) → EuclideanSpace ℝ (Fin (G.n + 1))) = _
  rw [gdet_cons_orth, gram_ext_tail, EuclideanSpace.norm_single]
  · norm_num; ring
  · intro j; rw [inner_smul_right, inner_single_ιE, mul_zero]

lemma ext_vol : G.ext.vol = 16 * 2 ^ G.d * G.vol := by
  change ∏ i, ‖(Fin.cons (EuclideanSpace.single 0 16) (fun i => (2 : ℝ) • ιE (G.v i)) :
    Fin (G.d + 1) → EuclideanSpace ℝ (Fin (G.n + 1))) i‖ = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, norm_smul, norm_ιE, EuclideanSpace.norm_single,
    Real.norm_eq_abs, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  rw [vol]; norm_num; ring

lemma ext_good (hG : G.Good) : G.ext.Good := by
  obtain ⟨h1, h2, h3⟩ := hG
  have hg : 0 < gdet G.v := gdet_pos h1
  refine ⟨linearIndependent_of_gdet_ne_zero (by rw [gdet_ext]; positivity),
    fun (m : Fin (G.d + 1) → ℤ) hm => ?_, ?_⟩
  · have e := G.norm_ext_emb_sq (fun i => (m i : ℝ))
    by_cases ht : (Fin.tail m) = 0
    · have h0 : m 0 ≠ 0 := by
        intro h0; apply hm; funext i
        refine Fin.cases h0 (fun j => ?_) i
        exact congrFun ht j
      have : (1 : ℝ) ≤ (m 0 : ℝ) ^ 2 := by
        have h := Int.one_le_abs h0
        have : (1 : ℤ) ≤ m 0 ^ 2 := by rw [← sq_abs]; nlinarith
        exact_mod_cast this
      have h4 : 0 ≤ ‖G.emb (Fin.tail fun i => (m i : ℝ))‖ ^ 2 := by positivity
      have : 1 ≤ ‖G.ext.emb (fun i => (m i : ℝ))‖ ^ 2 := by
        have : (1 : ℝ) ≤ 256 * (m 0 : ℝ) ^ 2 + 4 * ‖G.emb (Fin.tail fun i => (m i : ℝ))‖ ^ 2 := by
          nlinarith
        exact this.trans_eq e.symm
      nlinarith [norm_nonneg (G.ext.emb (fun i => (m i : ℝ)))]
    · have := h2 (Fin.tail m) ht
      have e' : (Fin.tail fun i => (m i : ℝ)) = fun i => ((Fin.tail m i : ℤ) : ℝ) := rfl
      rw [e'] at e
      have : 1 ≤ ‖G.ext.emb (fun i => (m i : ℝ))‖ ^ 2 := by
        have : (1 : ℝ) ≤ 256 * (m 0 : ℝ) ^ 2 +
            4 * ‖G.emb (fun i => ((Fin.tail m i : ℤ) : ℝ))‖ ^ 2 := by
          nlinarith [sq_nonneg ((m 0 : ℝ))]
        exact this.trans_eq e.symm
      nlinarith [norm_nonneg (G.ext.emb (fun i => (m i : ℝ)))]
  · have hv := G.ext_vol
    unfold vol at hv
    change (∏ i, ‖G.ext.v i‖) ^ 2 ≤ 2 ^ ((G.d + 1) ^ 2) * gdet G.ext.v
    rw [hv, gdet_ext]
    have hpow : (2 : ℝ) ^ (G.d ^ 2) ≤ 2 ^ ((G.d + 1) ^ 2) :=
      pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left (Nat.le_succ _) 2)
    have e4 : ((2 : ℝ) ^ G.d) ^ 2 = 4 ^ G.d := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc (16 * 2 ^ G.d * ∏ i, ‖G.v i‖) ^ 2 = 256 * 4 ^ G.d * (∏ i, ‖G.v i‖) ^ 2 := by
          rw [mul_pow, mul_pow, e4]; norm_num
      _ ≤ 256 * 4 ^ G.d * (2 ^ (G.d ^ 2) * gdet G.v) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 256 * 4 ^ G.d * (2 ^ ((G.d + 1) ^ 2) * gdet G.v) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hg.le) (by positivity)
      _ = 2 ^ ((G.d + 1) ^ 2) * (256 * 4 ^ G.d * gdet G.v) := by ring

/-- The new function `F'(y, x) = clamp(F(x) + ε cos(2π y))`. -/
def extF (F : G.Pt → ℝ) (ε : ℝ) : G.ext.Pt → ℝ :=
  fun (y : Fin (G.d + 1) → UnitAddCircle) => clamp1 (F (Fin.tail y) + ε * (ec (y 0)).re)

lemma abs_extF_le (F : G.Pt → ℝ) (ε : ℝ) (y : G.ext.Pt) : |G.extF F ε y| ≤ 1 :=
  abs_clamp1_le _

lemma extF_isLip {F : G.Pt → ℝ} (hF : G.IsLip F) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 4) :
    G.ext.IsLip (G.extF F ε) := by
  intro (t : Fin (G.d + 1) → ℝ) (t' : Fin (G.d + 1) → ℝ)
  show |clamp1 (F (G.pt (Fin.tail t)) + ε * (ec ((t 0 : ℝ) : UnitAddCircle)).re) -
    clamp1 (F (G.pt (Fin.tail t')) + ε * (ec ((t' 0 : ℝ) : UnitAddCircle)).re)| ≤
      ‖G.ext.emb (t - t')‖
  refine (abs_clamp1_sub_le _ _).trans ?_
  set A := ‖G.emb (Fin.tail t - Fin.tail t')‖ with hA
  set B := |t 0 - t' 0| with hB
  have hFt : |F (G.pt (Fin.tail t)) - F (G.pt (Fin.tail t'))| ≤ A := hF _ _
  have hec : |(ec ((t 0 : ℝ) : UnitAddCircle)).re - (ec ((t' 0 : ℝ) : UnitAddCircle)).re| ≤
      2 * Real.pi * B := by
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    exact norm_toCircle_sub_le _ _
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := abs_nonneg _
  have key : |F (G.pt (Fin.tail t)) + ε * (ec ((t 0 : ℝ) : UnitAddCircle)).re -
      (F (G.pt (Fin.tail t')) + ε * (ec ((t' 0 : ℝ) : UnitAddCircle)).re)| ≤ A + 2 * B := by
    rw [show F (G.pt (Fin.tail t)) + ε * (ec ((t 0 : ℝ) : UnitAddCircle)).re -
      (F (G.pt (Fin.tail t')) + ε * (ec ((t' 0 : ℝ) : UnitAddCircle)).re) =
      (F (G.pt (Fin.tail t)) - F (G.pt (Fin.tail t'))) +
        ε * ((ec ((t 0 : ℝ) : UnitAddCircle)).re - (ec ((t' 0 : ℝ) : UnitAddCircle)).re) by ring]
    refine (abs_add_le _ _).trans (add_le_add hFt ?_)
    rw [abs_mul, abs_of_nonneg hε]
    calc ε * |(ec ((t 0 : ℝ) : UnitAddCircle)).re - (ec ((t' 0 : ℝ) : UnitAddCircle)).re|
        ≤ ε * (2 * Real.pi * B) := mul_le_mul_of_nonneg_left hec hε
      _ = (ε * Real.pi) * (2 * B) := by ring
      _ ≤ 1 * (2 * B) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [Real.pi_pos, Real.pi_lt_four]
      _ = 2 * B := one_mul _
  refine key.trans ?_
  have e := G.norm_ext_emb_sq (t - t')
  have hsq : (A + 2 * B) ^ 2 ≤ ‖G.ext.emb (t - t')‖ ^ 2 := by
    rw [e]
    have h0 : (t - t') 0 ^ 2 = B ^ 2 := by rw [hB, sq_abs]; rfl
    have h1 : Fin.tail (t - t') = Fin.tail t - Fin.tail t' := rfl
    rw [h0, h1]
    nlinarith [sq_nonneg (A - 2 * B)]
  exact (abs_le_of_sq_le_sq' hsq (norm_nonneg _)).2

end DTorus

end

end GT
end File_GT_TorusExt

section File_GT_BadEdB1
/-!
# Theorem 6.6, the quadratic case: generic tools

Dilation of regular distributions by units, mixtures of translates by `6(n + z)`, closure
properties of locally quadratic maps, and the telescoping of the four-term average.
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Dilation -/

lemma mu_image_mul {B : Finset (ZMod p)} {u v : ZMod p} (huv : u * v = 1) (m : ZMod p) :
    mu (B.image (u * ·)) (u * m) = mu B m := by
  have hinj : Function.Injective (u * · : ZMod p → ZMod p) := by
    intro a b hab
    have := congrArg (v * ·) hab
    simp only [← mul_assoc, mul_comm v u, huv, one_mul] at this
    exact this
  unfold mu
  rw [card_image_of_injective _ hinj]
  simp only [mem_image]
  congr 1
  apply propext
  constructor
  · rintro ⟨y, hy, hyx⟩; rwa [← hinj hyx]
  · intro h; exact ⟨m, h, rfl⟩

lemma regP_image_mul (S : Finset (ZMod p)) {u v : ZMod p} (huv : u * v = 1) (ρ : ℝ)
    (m : ZMod p) : regP (S.image (· * v)) ρ (u * m) = regP S ρ m := by
  unfold regP
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [bohr_image_mul S huv, mu_image_mul huv]

lemma sum_regP_image_mul (S : Finset (ZMod p)) {u v : ZMod p} (huv : u * v = 1) (ρ : ℝ)
    (g : ZMod p → ℝ) :
    ∑ x, regP (S.image (· * v)) ρ x * g x = ∑ m, regP S ρ m * g (u * m) := by
  have hvu : v * u = 1 := by rw [mul_comm]; exact huv
  let e : ZMod p ≃ ZMod p :=
    ⟨(u * ·), (v * ·), fun x => by simp [← mul_assoc, hvu], fun x => by simp [← mul_assoc, huv]⟩
  refine (Fintype.sum_equiv e _ _ fun m => ?_).symm
  change regP S ρ m * g (u * m) = regP (S.image (· * v)) ρ (u * m) * g (u * m)
  rw [regP_image_mul S huv]

/-! ### Mixtures of translates by `6(n + z)` -/

set_option maxHeartbeats 1000000 in
/-- If `a` is regular on `n₀ + B(S, ρ/2)`, `n` regular on `B(S, σ)`, and `m` is drawn from a
law `Q_a` with `Z a m` small, then `a + 6(n + Z a m)` is close in law to `a`. -/
theorem tv_mix6 {S : Finset (ZMod p)} {n0 : ZMod p} {ρ σ ρq : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hq : 0 ≤ ρq) (h4q : 4 * ρq ≤ σ) (h4σ : 24 * σ ≤ ρ / 2) (Q : ZMod p → ZMod p → ℝ)
    (Z : ZMod p → ZMod p → ZMod p)
    (hQ0 : ∀ a y, 0 ≤ Q a y) (hQ1 : ∀ a, ∑ y, Q a y = 1)
    (hQs : ∀ a y, Q a y ≠ 0 → snorm S (Z a y) ≤ ρq) (g : ZMod p → ℝ) {B : ℝ}
    (hg : ∀ x, |g x| ≤ B) :
    |∑ a, regP S (ρ / 2) (a - n0) * ∑ n, regP S σ n * ∑ y, Q a y * g (a + 6 * (n + Z a y)) -
        ∑ x, regP S (ρ / 2) (x - n0) * g x| ≤
      B * (50 * S.card * ρq / σ) + B * (50 * S.card * (6 * σ) / (ρ / 2)) := by
  have hP0 : ∀ a, 0 ≤ regP S (ρ / 2) (a - n0) := fun a => regP_nonneg _ _
  have hP1 : ∑ a, regP S (ρ / 2) (a - n0) = 1 := sum_regP_center S (by positivity) n0
  have hU0 : ∀ t, 0 ≤ regP S σ t := fun t => regP_nonneg _ _
  have hU1 : ∑ t, regP S σ t = 1 := sum_regP S hσ.le
  have step1 : ∀ a, |∑ n, regP S σ n * ∑ y, Q a y * g (a + 6 * (n + Z a y)) -
      ∑ n, regP S σ n * g (a + 6 * n)| ≤ B * (50 * S.card * ρq / σ) := by
    intro a
    have e1 : ∑ n, regP S σ n * ∑ y, Q a y * g (a + 6 * (n + Z a y)) =
        ∑ y, Q a y * ∑ n, regP S σ n * g (a + 6 * (n + Z a y)) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun y _ => sum_congr rfl fun n _ => by ring
    have e2 : ∑ n, regP S σ n * g (a + 6 * n) = ∑ y, Q a y * ∑ n, regP S σ n * g (a + 6 * n) := by
      rw [← sum_mul, hQ1, one_mul]
    rw [e1, e2, ← sum_sub_distrib]
    simp_rw [← mul_sub]
    refine abs_wavg_le (hQ0 a) (hQ1 a) _ fun y hy => ?_
    have hyb : Z a y ∈ bohr S ρq := (mem_bohr_iff_snorm hq).mpr (hQs a y hy)
    exact regP_shift_real subset_rfl hσ hq h4q hyb (fun n => g (a + 6 * n)) (fun x => hg _)
  have step2 : |∑ a, regP S (ρ / 2) (a - n0) * ∑ n, regP S σ n * g (a + 6 * n) -
      ∑ x, regP S (ρ / 2) (x - n0) * g x| ≤ B * (50 * S.card * (6 * σ) / (ρ / 2)) := by
    have e1 : ∑ a, regP S (ρ / 2) (a - n0) * ∑ n, regP S σ n * g (a + 6 * n) =
        ∑ n, regP S σ n * ∑ x, regP S (ρ / 2) (x - n0) * g (x + 6 * n) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun n _ => sum_congr rfl fun a _ => by ring
    have e2 : ∑ x, regP S (ρ / 2) (x - n0) * g x =
        ∑ n, regP S σ n * ∑ x, regP S (ρ / 2) (x - n0) * g x := by
      rw [← sum_mul, hU1, one_mul]
    rw [e1, e2, ← sum_sub_distrib]
    simp_rw [← mul_sub]
    refine abs_wavg_le hU0 hU1 _ fun n hn => ?_
    have hnb : snorm S n ≤ σ := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hσ.le hn) hσ.le
    have h6 : snorm S (6 * n) ≤ 6 * σ := by
      have := snorm_nsmul_le (S := S) 6 n
      push_cast at this; linarith
    exact shift_real_c subset_rfl (by positivity) (by linarith) h6 n0 g hg
  have hcomb : |∑ a, regP S (ρ / 2) (a - n0) * ∑ n, regP S σ n * ∑ y, Q a y *
      g (a + 6 * (n + Z a y)) -
      ∑ a, regP S (ρ / 2) (a - n0) * ∑ n, regP S σ n * g (a + 6 * n)| ≤
      B * (50 * S.card * ρq / σ) := by
    rw [← sum_sub_distrib]
    simp_rw [← mul_sub]
    exact abs_wavg_le hP0 hP1 _ fun a _ => step1 a
  calc _ = |(∑ a, regP S (ρ / 2) (a - n0) * ∑ n, regP S σ n * ∑ y, Q a y *
        g (a + 6 * (n + Z a y)) -
        ∑ a, regP S (ρ / 2) (a - n0) * ∑ n, regP S σ n * g (a + 6 * n)) +
        (∑ a, regP S (ρ / 2) (a - n0) * ∑ n, regP S σ n * g (a + 6 * n) -
        ∑ x, regP S (ρ / 2) (x - n0) * g x)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hcomb step2)

/-! ### Locally quadratic maps -/

section lq

variable {M : Type*} [AddCommGroup M]

lemma LocQuad.add' {B : Set (ZMod p)} {Ξ Ψ : ZMod p → M} (h1 : LocQuad B Ξ) (h2 : LocQuad B Ψ) :
    LocQuad B (fun x => Ξ x + Ψ x) := by
  intro n a b c m0 m1 m2 m3 m12 m13 m23 m123
  have e1 := h1 n a b c m0 m1 m2 m3 m12 m13 m23 m123
  have e2 := h2 n a b c m0 m1 m2 m3 m12 m13 m23 m123
  have h := congrArg₂ (· + ·) e1 e2
  simp only [add_zero] at h
  try simp only
  rw [← h]
  abel

lemma LocQuad.const' (B : Set (ZMod p)) (c : M) : LocQuad B (fun _ => c) := by
  intro n a b d _ _ _ _ _ _ _ _
  abel

lemma LocQuad.of_hom (B : Set (ZMod p)) (f : ZMod p →+ M) : LocQuad B (fun x => f x) := by
  intro n a b c _ _ _ _ _ _ _ _
  simp only [map_add]
  abel

lemma LocQuad.cons {d : ℕ} {B : Set (ZMod p)} {a : ZMod p → UnitAddCircle}
    {Ξ : ZMod p → Fin d → UnitAddCircle} (ha : LocQuad B a) (hΞ : LocQuad B Ξ) :
    LocQuad B (fun x => (Fin.cons (a x) (Ξ x) : Fin (d + 1) → UnitAddCircle)) := by
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have e1 := ha n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have e2 := hΞ n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using e1
  · have := congrFun e2 j
    simpa using this

/-- Locally quadratic maps pull back under the affine map `l ↦ (l - n') v`. -/
lemma LocQuad.affine {S : Finset (ZMod p)} {ρ : ℝ} (hρ : 0 ≤ ρ) {φ : ZMod p → M}
    (hL : LocQuad (sBohr S 0 ρ) φ) (n' v : ZMod p) :
    LocQuad (sBohr (S.image (· * v)) n' ρ) (fun l => φ ((l - n') * v)) := by
  have hmem : ∀ x, x ∈ sBohr (S.image (· * v)) n' ρ → (x - n') * v ∈ sBohr S 0 ρ := by
    intro x hx
    rw [mem_sBohr hρ] at hx ⊢
    rw [snorm_image_mul] at hx
    rw [sub_zero, mul_comm]; exact hx
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have key := hL ((n - n') * v) (h1 * v) (h2 * v) (h3 * v) (by simpa using hmem _ m0)
    (by have := hmem _ m1; ring_nf at this ⊢; exact this)
    (by have := hmem _ m2; ring_nf at this ⊢; exact this)
    (by have := hmem _ m3; ring_nf at this ⊢; exact this)
    (by have := hmem _ m12; ring_nf at this ⊢; exact this)
    (by have := hmem _ m13; ring_nf at this ⊢; exact this)
    (by have := hmem _ m23; ring_nf at this ⊢; exact this)
    (by have := hmem _ m123; ring_nf at this ⊢; exact this)
  try simp only
  convert key using 3 <;> ring_nf

end lq

/-! ### Telescoping the four-term average -/

/-- The slot functions for the `i`-th telescoping term. -/
def telH (i : Fin 4) (f F : ZMod p → ℝ) (j : Fin 4) : ZMod p → ℝ :=
  if j < i then F else if j = i then fun x => (f x - F x) / 2 else f

lemma telH_self (i : Fin 4) (f F : ZMod p → ℝ) (x : ZMod p) :
    telH i f F i x = (f x - F x) / 2 := by
  simp [telH]

lemma abs_telH_le {f F : ZMod p → ℝ} (hf : ∀ x, |f x| ≤ 1) (hF : ∀ x, |F x| ≤ 1) (i j : Fin 4)
    (x : ZMod p) : |telH i f F j x| ≤ 1 := by
  unfold telH
  split_ifs
  · exact hF x
  · have h1 := hf x; have h2 := hF x
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
  · exact hf x

lemma telescope4 (f F : ZMod p → ℝ) (a r : ZMod p) :
    f a * f (a + r) * f (a + 2 * r) * f (a + 3 * r) -
      F a * F (a + r) * F (a + 2 * r) * F (a + 3 * r) =
    2 * ∑ i : Fin 4, ap4 (telH i f F) a r := by
  simp only [Fin.sum_univ_four, ap4, telH]
  simp
  ring

end

end GT
end File_GT_BadEdB1

section File_GT_BadEdB2
/-!
# Theorem 6.6, the quadratic case: the new approximant

Every label `c` is replaced by the labels `(c, a, n)`, `a` drawn from `n_c + B(S_c, ρ_c/2)` and
`n` from `B(S_c, ρ₀_c)`.  The label `(c, a, n)` has centre `a + 6n`, frequencies
`(6k)^{-1} S'`, radius `2ρ_m`, the torus `G_c × ℝ/ℤ`, the function
`clamp(F_c(x) + ε cos 2πy)` and the map `l ↦ (γ((l - a - 6n)/(6k)), Ξ_c(l))`, where
`k, S', φ, β, ε` are data attached to `(c, a)` and `γ(m) = φ(m) + β(n) m / p + τ`.
-/

open Finset KM

namespace GT

noncomputable section

/-- The data attached to a pair `(c, a)`. -/
structure EDat (p : ℕ) where
  k : ℕ
  S : Finset (ZMod p)
  φ : ZMod p → UnitAddCircle
  β : ZMod p → ZMod p
  ε : ℝ

variable {p : ℕ} [NeZero p]

/-- The dilation factor `6k`. -/
def EDat.u (e : EDat p) : ZMod p := ((6 * e.k : ℕ) : ZMod p)

/-- The phase `γ(m) = φ(m) + β(n) m / p + τ`. -/
def EDat.gam (e : EDat p) (n : ZMod p) (τ : UnitAddCircle) (m : ZMod p) : UnitAddCircle :=
  e.φ m + ZMod.toAddCircle (e.β n * m) + τ

namespace SLA

variable (v : SLA p) (η θ : ℝ) (T : ℕ)

/-- The scale `ρ₀_c` of `n`. -/
def ρ0 (c : v.C) : ℝ := θ * eps4 η * v.ρ c

/-- The scale `ρ_m = θ^T ρ₀_c` of `m`. -/
def ρm (c : v.C) : ℝ := θ ^ T * v.ρ0 η θ c

/-- The label `(c, a, n)` is in the essential range. -/
def ECond (c : v.C) (a n : ZMod p) : Prop :=
  regP (v.S c) (v.ρ c / 2) (a - v.n c) ≠ 0 ∧ regP (v.S c) (v.ρ0 η θ c) n ≠ 0

/-- The weight of the label `(c, a, n)`. -/
def eprob (c' : v.C × ZMod p × ZMod p) : ℝ :=
  v.prob c'.1 * regP (v.S c'.1) (v.ρ c'.1 / 2) (c'.2.1 - v.n c'.1) *
    regP (v.S c'.1) (v.ρ0 η θ c'.1) c'.2.2

open Classical in
/-- The data of the label `(c, a, n)`. -/
def edata (ed : v.C → ZMod p → EDat p) (τ : v.C → ZMod p → ZMod p → UnitAddCircle)
    (c' : v.C × ZMod p × ZMod p) : LData p where
  n := c'.2.1 + 6 * c'.2.2
  S := (ed c'.1 c'.2.1).S.image (· * (ed c'.1 c'.2.1).u⁻¹)
  ρ := 2 * v.ρm η θ T c'.1
  G := (v.G c'.1).ext
  F := (v.G c'.1).extF (v.F c'.1) (ed c'.1 c'.2.1).ε
  Ξ := fun l => if v.ECond η θ c'.1 c'.2.1 c'.2.2 then
      (Fin.cons ((ed c'.1 c'.2.1).gam c'.2.2 (τ c'.1 c'.2.1 c'.2.2)
        ((l - (c'.2.1 + 6 * c'.2.2)) * (ed c'.1 c'.2.1).u⁻¹)) (v.Ξ c'.1 l) :
        Fin ((v.G c'.1).d + 1) → UnitAddCircle) else 0

/-- The new structured local approximant. -/
def enew (ed : v.C → ZMod p → EDat p) (τ : v.C → ZMod p → ZMod p → UnitAddCircle) : SLA p :=
  ofData (v.C × ZMod p × ZMod p) (v.eprob η θ) (v.edata η θ T ed τ)

/-- The properties of the data attached to `(c, a)`. -/
def EProp (K : ℝ) (c : v.C) (e : EDat p) : Prop :=
  1 ≤ e.k ∧ (e.k : ℝ) ≤ K ∧ e.u ≠ 0 ∧ v.S c ⊆ e.S ∧ 0 ≤ e.ε ∧ e.ε ≤ 1 / 4 ∧
    LocQuad (sBohr e.S 0 (2 * v.ρm η θ T c)) e.φ

/-- The numerical conditions attached to a label `c`. -/
def ENum (K E : ℝ) (c : v.C) : Prop :=
  0 < θ ∧ 0 < v.ρm η θ T c ∧ 2 * v.ρm η θ T c ≤ 1 ∧ 4 * (K * v.ρm η θ T c) ≤ v.ρ0 η θ c ∧
    24 * v.ρ0 η θ c ≤ v.ρ c / 2 ∧ 6 * v.ρ0 η θ c + 12 * (K * v.ρm η θ T c) ≤ v.ρ c / 2 ∧
    50 * (v.S c).card * (K * v.ρm η θ T c) / v.ρ0 η θ c +
      50 * (v.S c).card * (6 * v.ρ0 η θ c) / (v.ρ c / 2) ≤ E

variable {v η θ T}

lemma ρ0_pos (hv : v.Valid) (hθ : 0 < θ) (c : v.C) : 0 < v.ρ0 η θ c := by
  have := (hv.2.2.2.1 c).1
  unfold ρ0 eps4; positivity

lemma eprob_nonneg (hv : v.Valid) (c' : v.C × ZMod p × ZMod p) : 0 ≤ v.eprob η θ c' :=
  mul_nonneg (mul_nonneg (hv.1 _) (regP_nonneg _ _)) (regP_nonneg _ _)

lemma sum_eprob (hv : v.Valid) (hθ : 0 < θ) : ∑ c', v.eprob η θ c' = 1 := by
  unfold eprob
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [← hv.2.1]
  refine sum_congr rfl fun c _ => ?_
  simp_rw [mul_assoc, ← mul_sum, ← sum_mul]
  rw [sum_regP _ (ρ0_pos hv hθ c).le, sum_regP_center _ (by linarith [(hv.2.2.2.1 c).1]),
    one_mul, mul_one]

lemma sum_enew (ed : v.C → ZMod p → EDat p) (τ : v.C → ZMod p → ZMod p → UnitAddCircle)
    (Φ : LData p → ℝ) :
    ∑ c', v.eprob η θ c' * Φ (v.edata η θ T ed τ c') =
      ∑ c, v.prob c * ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
        ∑ n, regP (v.S c) (v.ρ0 η θ c) n * Φ (v.edata η θ T ed τ (c, a, n)) := by
  unfold eprob
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => ?_
  simp_rw [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun n _ => ?_
  ring

/-- Validity of a new label. -/
lemma edata_OK (hp : p.Prime) (hv : v.Valid) {K E : ℝ} {ed : v.C → ZMod p → EDat p}
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) {c : v.C} {a n : ZMod p}
    (hE : v.EProp η θ T K c (ed c a)) (hN : v.ENum η θ T K E c) :
    (v.edata η θ T ed τ (c, a, n)).OK := by
  classical
  haveI := Fact.mk hp
  obtain ⟨hk1, hkK, hu, hSS, hε0, hε1, hφ⟩ := hE
  obtain ⟨hθ, hm0, hm1, h4K, h24, hbud, -⟩ := hN
  obtain ⟨s, hs, hs0⟩ := hv.2.2.1 c
  have hρ0 := (hv.2.2.2.1 c).1
  have hρ00 := ρ0_pos (η := η) hv hθ c
  refine ⟨⟨s * (ed c a).u⁻¹, mem_image_of_mem _ (hSS hs), mul_ne_zero hs0 (inv_ne_zero hu)⟩,
    ⟨by change 0 < 2 * v.ρm η θ T c; linarith, hm1⟩, DTorus.extF_isLip _ (hv.2.2.2.2.1 c) hε0 hε1,
    fun x => DTorus.abs_extF_le _ _ _ _, ?_, DTorus.ext_good _ (hv.2.2.2.2.2.2.2 c)⟩
  change LocQuad (sBohr ((ed c a).S.image (· * (ed c a).u⁻¹)) (a + 6 * n)
    (2 * v.ρm η θ T c)) (fun l => if v.ECond η θ c a n then
      (Fin.cons ((ed c a).gam n (τ c a n) ((l - (a + 6 * n)) * (ed c a).u⁻¹)) (v.Ξ c l) :
        Fin ((v.G c).d + 1) → UnitAddCircle) else 0)
  by_cases hC : v.ECond η θ c a n
  · simp only [if_pos hC]
    have h2m : (0 : ℝ) ≤ 2 * v.ρm η θ T c := by positivity
    refine LocQuad.cons ?_ ?_
    · unfold EDat.gam
      refine LocQuad.add' (LocQuad.add' (hφ.affine h2m _ _) ?_) (LocQuad.const' _ _)
      exact LocQuad.affine (φ := fun m => ZMod.toAddCircle ((ed c a).β n * m)) h2m
        (LocQuad.of_hom _ ((ZMod.toAddCircle).comp (AddMonoidHom.mulLeft ((ed c a).β n)))) _ _
    · refine (hv.2.2.2.2.2.2.1 c).mono ?_
      intro x hx
      rw [mem_sBohr h2m] at hx
      change x ∈ sBohr (v.S c) (v.n c) (v.ρ c)
      rw [mem_sBohr hρ0.le]
      have h1 : snorm (v.S c) (x - (a + 6 * n)) ≤ (6 * (ed c a).k : ℕ) * (2 * v.ρm η θ T c) := by
        refine (snorm_mono hSS _).trans ?_
        refine (snorm_le_of_image_inv hp _ _ hu _).trans ?_
        exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
      have ha := snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) hC.1) (by positivity)
      have hn := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ00.le hC.2) hρ00.le
      have h6 : snorm (v.S c) (6 * n) ≤ 6 * v.ρ0 η θ c := by
        have := snorm_nsmul_le (S := v.S c) 6 n
        push_cast at this; linarith
      have e : x - v.n c = (a - v.n c) + 6 * n + (x - (a + 6 * n)) := by ring
      rw [e]
      refine (snorm_add_le _ _).trans ?_
      have := snorm_add_le (S := v.S c) (a - v.n c) (6 * n)
      push_cast at h1
      have hkm : (ed c a).k * v.ρm η θ T c ≤ K * v.ρm η θ T c :=
        mul_le_mul_of_nonneg_right hkK hm0.le
      nlinarith
  · simp only [if_neg hC]
    exact LocQuad.const' _ _

/-- Validity of the new approximant. -/
theorem enew_valid (hp : p.Prime) (hv : v.Valid) {K E : ℝ} {ed : v.C → ZMod p → EDat p}
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) (hθ : 0 < θ)
    (hE : ∀ c a, v.EProp η θ T K c (ed c a)) (hN : ∀ c, v.ENum η θ T K E c) :
    (v.enew η θ T ed τ).Valid :=
  ofData_valid _ _ _ (eprob_nonneg hv) (sum_eprob hv hθ) fun c' =>
    edata_OK hp hv τ (hE c'.1 c'.2.1) (hN c'.1)

/-- The label average of the new label, as an average over `m`. -/
lemma edata_avg (hp : p.Prime) {K : ℝ} {ed : v.C → ZMod p → EDat p}
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) {c : v.C} {a n : ZMod p}
    (hE : v.EProp η θ T K c (ed c a)) (g : ZMod p → ℝ) :
    (v.edata η θ T ed τ (c, a, n)).avg g =
      ∑ m, regP (ed c a).S (v.ρm η θ T c) m * g (a + 6 * (n + (ed c a).k * m)) := by
  haveI := Fact.mk hp
  rw [avg_shift]
  change ∑ y, regP ((ed c a).S.image (· * (ed c a).u⁻¹)) (2 * v.ρm η θ T c / 2) y *
    g (a + 6 * n + y) = _
  rw [show 2 * v.ρm η θ T c / 2 = v.ρm η θ T c by ring]
  rw [sum_regP_image_mul _ (mul_inv_cancel₀ hE.2.2.1)]
  refine sum_congr rfl fun m _ => ?_
  congr 2
  unfold EDat.u; push_cast; ring

/-- **Waste**: expectations of bounded functions barely change. -/
theorem ex_enew (hp : p.Prime) (hv : v.Valid) {K E : ℝ} {ed : v.C → ZMod p → EDat p}
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) (hθ : 0 < θ)
    (hE : ∀ c a, v.EProp η θ T K c (ed c a)) (hN : ∀ c, v.ENum η θ T K E c)
    (g : ZMod p → ℝ) {B : ℝ} (hg : ∀ x, |g x| ≤ B) :
    |((v.enew η θ T ed τ).triple η).ex g - (v.triple η).ex g| ≤ B * E := by
  have heps : 0 ≤ eps4 η := (Real.exp_pos _).le
  have hv' := enew_valid hp hv τ hθ hE hN
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg 0)
  rw [ex_eq _ η heps (fun c' => (hv'.2.2.2.1 c').1.le),
    ex_eq v η heps (fun c => (hv.2.2.2.1 c).1.le)]
  change |∑ c', v.eprob η θ c' * (v.edata η θ T ed τ c').avg g - _| ≤ _
  rw [sum_enew _ _ (fun L => L.avg g), ← sum_sub_distrib]
  simp_rw [← mul_sub]
  refine abs_wavg_le hv.1 hv.2.1 _ fun c _ => ?_
  obtain ⟨-, hm0, -, h4K, h24, -, hnum⟩ := hN c
  have hρ0 := (hv.2.2.2.1 c).1
  have hρ00 := ρ0_pos (η := η) hv hθ c
  have e : ∀ a n, (v.edata η θ T ed τ (c, a, n)).avg g =
      ∑ m, regP (ed c a).S (v.ρm η θ T c) m * g (a + 6 * (n + (ed c a).k * m)) :=
    fun a n => edata_avg hp τ (hE c a) g
  simp only [e]
  have hmix := tv_mix6 (S := v.S c) (n0 := v.n c) hρ0 hρ00
    (mul_nonneg ((Nat.cast_nonneg _).trans (hE c (0 : ZMod p)).2.1) hm0.le) h4K h24
    (fun a m => regP (ed c a).S (v.ρm η θ T c) m) (fun a m => ((ed c a).k : ZMod p) * m)
    (fun a m => regP_nonneg _ _) (fun a => sum_regP _ hm0.le) (fun a m hm => by
      have hmb := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hm0.le hm) hm0.le
      have h1 := snorm_nsmul_le (S := v.S c) (ed c a).k m
      have h2 := snorm_mono (hE c a).2.2.2.1 m
      have hk0 : (0 : ℝ) ≤ (ed c a).k := Nat.cast_nonneg _
      calc snorm (v.S c) (((ed c a).k : ZMod p) * m) ≤ (ed c a).k * snorm (ed c a).S m :=
            h1.trans (mul_le_mul_of_nonneg_left h2 hk0)
        _ ≤ K * v.ρm η θ T c :=
            mul_le_mul (hE c a).2.1 hmb (snorm_nonneg _) ((hk0.trans (hE c a).2.1))) g hg
  refine hmix.trans ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left hnum hB

end SLA

end

end GT
end File_GT_BadEdB2

section File_GT_BadEdB3
/-!
# Theorem 6.6, the quadratic case: statistics of the new approximant

Structural bounds (`d₁`, `d₂`, `ρ`, `vol`) and the energy bound.
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

namespace SLA

variable {v : SLA p} {η θ : ℝ} {T : ℕ}

theorem d1_enew (ed : v.C → ZMod p → EDat p) (τ : v.C → ZMod p → ZMod p → UnitAddCircle)
    {J : ℝ} (hJ0 : 0 ≤ J) (hS : ∀ c a, ((ed c a).S.card : ℝ) ≤ (v.S c).card + J) :
    ((v.enew η θ T ed τ).d1 : ℝ) ≤ v.d1 + J := by
  classical
  have hle : ∀ c, (v.S c).card ≤ v.d1 := fun c =>
    Finset.le_sup (f := fun c => (v.S c).card) (mem_univ c)
  rcases isEmpty_or_nonempty (v.enew η θ T ed τ).C with hC | hC
  · have : (v.enew η θ T ed τ).d1 = 0 := by
      unfold SLA.d1; rw [univ_eq_empty, sup_empty]; rfl
    rw [this]; push_cast; positivity
  obtain ⟨c', -, hc'⟩ := Finset.exists_mem_eq_sup (univ : Finset (v.enew η θ T ed τ).C)
    univ_nonempty (fun c => ((v.enew η θ T ed τ).S c).card)
  have e : (v.enew η θ T ed τ).d1 = ((v.enew η θ T ed τ).S c').card := hc'
  rw [e]
  obtain ⟨c, a, n⟩ := c'
  change ((((ed c a).S.image (· * (ed c a).u⁻¹))).card : ℝ) ≤ _
  have h1 : ((ed c a).S.image (· * (ed c a).u⁻¹)).card ≤ (ed c a).S.card := card_image_le
  have h2 : ((v.S c).card : ℝ) ≤ v.d1 := by exact_mod_cast hle c
  have h1' : (((ed c a).S.image (· * (ed c a).u⁻¹)).card : ℝ) ≤ (ed c a).S.card := by
    exact_mod_cast h1
  linarith [hS c a]

theorem d2_enew (ed : v.C → ZMod p → EDat p) (τ : v.C → ZMod p → ZMod p → UnitAddCircle) :
    (v.enew η θ T ed τ).d2 ≤ v.d2 + 1 := by
  unfold SLA.d2
  refine Finset.sup_le fun c' _ => ?_
  obtain ⟨c, a, n⟩ := c'
  have hc : (v.G c).d ≤ univ.sup fun c => (v.G c).d := Finset.le_sup (f := fun c => (v.G c).d)
    (mem_univ c)
  change (v.G c).d + 1 ≤ _
  omega

theorem rmin_enew (hv : v.Valid) (ed : v.C → ZMod p → EDat p)
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ c, L * v.ρ c ≤ 2 * v.ρm η θ T c) :
    L * v.rmin ≤ (v.enew η θ T ed τ).rmin := by
  haveI := nonempty_C hv
  have hle : ∀ c, v.rmin ≤ v.ρ c := fun c => by
    unfold SLA.rmin; exact ciInf_le (Finite.bddBelow_range _) c
  haveI : Nonempty (v.enew η θ T ed τ).C := (inferInstance : Nonempty (v.C × ZMod p × ZMod p))
  unfold SLA.rmin
  refine le_ciInf fun c' => ?_
  obtain ⟨c, a, n⟩ := c'
  change _ ≤ 2 * v.ρm η θ T c
  refine le_trans ?_ (hL c)
  exact mul_le_mul_of_nonneg_left (hle c) hL0

theorem volm_enew (hv : v.Valid) (ed : v.C → ZMod p → EDat p)
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) :
    (v.enew η θ T ed τ).volm ≤ 16 * 2 ^ v.d2 * v.volm := by
  haveI := nonempty_C hv
  have hle : ∀ c, (v.G c).vol ≤ v.volm := fun c => by
    unfold SLA.volm; exact le_ciSup (Finite.bddAbove_range (fun c => (v.G c).vol)) c
  have hd : ∀ c, (v.G c).d ≤ v.d2 := fun c =>
    Finset.le_sup (f := fun c => (v.G c).d) (mem_univ c)
  haveI : Nonempty (v.enew η θ T ed τ).C := (inferInstance : Nonempty (v.C × ZMod p × ZMod p))
  conv_lhs => unfold SLA.volm
  refine ciSup_le fun c' => ?_
  obtain ⟨c, a, n⟩ := c'
  change (v.G c).ext.vol ≤ _
  rw [DTorus.ext_vol]
  have h2 : (2 : ℝ) ^ (v.G c).d ≤ 2 ^ v.d2 := pow_le_pow_right₀ (by norm_num) (hd c)
  have := hle c
  have h0 := (v.G c).vol_nonneg
  calc 16 * 2 ^ (v.G c).d * (v.G c).vol ≤ 16 * 2 ^ v.d2 * (v.G c).vol := by gcongr
    _ ≤ _ := by gcongr

lemma split_avg {α β : Type*} [Fintype α] [Fintype β] {P : α → ℝ} {Q : β → ℝ}
    (hP : ∑ n, P n = 1) (hQ : ∑ m, Q m = 1) (g X : α → β → ℝ) (A B : ℝ) :
    ∑ n, P n * ∑ m, Q m * (g n m - A * X n m + B) =
      ∑ n, P n * ∑ m, Q m * g n m - (A * ∑ n, P n * ∑ m, Q m * X n m - B) := by
  have e : ∀ n, ∑ m, Q m * (g n m - A * X n m + B) =
      ∑ m, Q m * g n m - A * ∑ m, Q m * X n m + B := by
    intro n
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul, hQ, one_mul,
      mul_sum]
    congr 1; congr 1
    exact sum_congr rfl fun m _ => by ring
  simp only [e]
  have e2 : ∀ n, P n * (∑ m, Q m * g n m - A * ∑ m, Q m * X n m + B) =
      P n * ∑ m, Q m * g n m - A * (P n * ∑ m, Q m * X n m) + B * P n := fun n => by ring
  simp only [e2, sum_add_distrib, sum_sub_distrib, ← mul_sum, hP]
  ring

/-- The correlation attached to `(c, a)`. -/
def ecorr (v : SLA p) (η θ : ℝ) (T : ℕ) (f : ZMod p → ℝ) (ed : v.C → ZMod p → EDat p)
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) (c : v.C) (a : ZMod p) : ℝ :=
  ∑ n, regP (v.S c) (v.ρ0 η θ c) n * ∑ m, regP (ed c a).S (v.ρm η θ T c) m *
    ((f (a + 6 * (n + (ed c a).k * m)) - v.F c (v.Ξ c (a + 6 * (n + (ed c a).k * m)))) / 2 *
      (ec ((ed c a).gam n (τ c a n) m)).re)

lemma edata_energy_le (hp : p.Prime) {K : ℝ} {ed : v.C → ZMod p → EDat p}
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) {c : v.C} {a n : ZMod p}
    (hE : v.EProp η θ T K c (ed c a)) (hC : v.ECond η θ c a n) (f : ZMod p → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (v.edata η θ T ed τ (c, a, n)).avg (fun x => (f x - (v.edata η θ T ed τ (c, a, n)).F
      ((v.edata η θ T ed τ (c, a, n)).Ξ x)) ^ 2) ≤
    ∑ m, regP (ed c a).S (v.ρm η θ T c) m *
      ((f (a + 6 * (n + (ed c a).k * m)) - v.F c (v.Ξ c (a + 6 * (n + (ed c a).k * m)))) ^ 2 -
        4 * (ed c a).ε * ((f (a + 6 * (n + (ed c a).k * m)) -
          v.F c (v.Ξ c (a + 6 * (n + (ed c a).k * m)))) / 2 *
          (ec ((ed c a).gam n (τ c a n) m)).re) + (ed c a).ε ^ 2) := by
  classical
  haveI := Fact.mk hp
  rw [edata_avg hp τ hE]
  refine sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (regP_nonneg _ _)
  set y := a + 6 * (n + (ed c a).k * m) with hy
  have hym : (y - (a + 6 * n)) * (ed c a).u⁻¹ = m := by
    rw [hy]
    have : a + 6 * (n + ((ed c a).k : ZMod p) * m) - (a + 6 * n) = (ed c a).u * m := by
      unfold EDat.u; push_cast; ring
    rw [this, mul_comm, ← mul_assoc, inv_mul_cancel₀ hE.2.2.1, one_mul]
  have hΞ : (v.edata η θ T ed τ (c, a, n)).Ξ y =
      (Fin.cons ((ed c a).gam n (τ c a n) m) (v.Ξ c y) : Fin ((v.G c).d + 1) → UnitAddCircle) := by
    change (if v.ECond η θ c a n then
      (Fin.cons ((ed c a).gam n (τ c a n) ((y - (a + 6 * n)) * (ed c a).u⁻¹)) (v.Ξ c y) :
        Fin ((v.G c).d + 1) → UnitAddCircle) else 0) = _
    rw [if_pos hC, hym]
  have hF : (v.edata η θ T ed τ (c, a, n)).F ((v.edata η θ T ed τ (c, a, n)).Ξ y) =
      clamp1 (v.F c (v.Ξ c y) + (ed c a).ε * (ec ((ed c a).gam n (τ c a n) m)).re) := by
    rw [hΞ]
    change clamp1 (v.F c (Fin.tail (Fin.cons _ (v.Ξ c y) : Fin ((v.G c).d + 1) → UnitAddCircle)) +
      _ * (ec ((Fin.cons _ (v.Ξ c y) : Fin ((v.G c).d + 1) → UnitAddCircle) 0)).re) = _
    rw [Fin.tail_cons, Fin.cons_zero]
  rw [hF]
  have hfy : |f y| ≤ 1 := abs_le.2 ⟨by linarith [(hf y).1], (hf y).2⟩
  refine (sq_sub_clamp1_le hfy _).trans ?_
  set R := (ec ((ed c a).gam n (τ c a n) m)).re
  have hR : R ^ 2 ≤ 1 := by
    have h1 : |R| ≤ 1 := (Complex.abs_re_le_norm _).trans (le_of_eq (norm_ec _))
    rw [← sq_abs]; nlinarith [abs_nonneg R]
  have hε : 0 ≤ (ed c a).ε := hE.2.2.2.2.1
  have : (ed c a).ε ^ 2 * R ^ 2 ≤ (ed c a).ε ^ 2 := by
    nlinarith [sq_nonneg (ed c a).ε]
  nlinarith

/-- **Energy** of the new approximant. -/
theorem energy_enew (hp : p.Prime) (hv : v.Valid) {K E : ℝ} {ed : v.C → ZMod p → EDat p}
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) (hθ : 0 < θ)
    (hE : ∀ c a, v.EProp η θ T K c (ed c a)) (hN : ∀ c, v.ENum η θ T K E c)
    (f : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ((v.enew η θ T ed τ).triple η).energy f ≤ (v.triple η).energy f + 4 * E -
      ∑ c, v.prob c * ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
        (4 * (ed c a).ε * v.ecorr η θ T f ed τ c a - (ed c a).ε ^ 2) := by
  have heps : 0 ≤ eps4 η := (Real.exp_pos _).le
  have hv' := enew_valid hp hv τ hθ hE hN
  rw [energy_eq _ η heps (fun c' => (hv'.2.2.2.1 c').1.le),
    energy_eq v η heps (fun c => (hv.2.2.2.1 c).1.le)]
  set Φ : LData p → ℝ := fun L => L.avg (fun x => (f x - L.F (L.Ξ x)) ^ 2) with hΦ
  change ∑ c', v.eprob η θ c' * Φ (v.edata η θ T ed τ c') ≤ _
  rw [sum_enew _ _ Φ]
  have hsum : ∑ c, v.prob c * (v.ldata c).avg (fun x => (f x - v.F c (v.Ξ c x)) ^ 2) + 4 * E -
      ∑ c, v.prob c * ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
        (4 * (ed c a).ε * v.ecorr η θ T f ed τ c a - (ed c a).ε ^ 2) =
      ∑ c, v.prob c * ((v.ldata c).avg (fun x => (f x - v.F c (v.Ξ c x)) ^ 2) + 4 * E -
        ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
          (4 * (ed c a).ε * v.ecorr η θ T f ed τ c a - (ed c a).ε ^ 2)) := by
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul, hv.2.1, one_mul]
  rw [hsum]
  refine sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (hv.1 c)
  obtain ⟨-, hm0, -, h4K, h24, -, hnum⟩ := hN c
  have hρ0 := (hv.2.2.2.1 c).1
  have hρ00 := ρ0_pos (η := η) hv hθ c
  set g : ZMod p → ℝ := fun x => (f x - v.F c (v.Ξ c x)) ^ 2 with hg
  set Q : ZMod p → ZMod p → ℝ := fun a m => regP (ed c a).S (v.ρm η θ T c) m with hQ
  have hQ1 : ∀ a, ∑ m, Q a m = 1 := fun a => sum_regP _ hm0.le
  -- pointwise bound
  have h1 : ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
      ∑ n, regP (v.S c) (v.ρ0 η θ c) n * Φ (v.edata η θ T ed τ (c, a, n)) ≤
      ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) * ∑ n, regP (v.S c) (v.ρ0 η θ c) n *
        ∑ m, Q a m * (g (a + 6 * (n + (ed c a).k * m)) -
          4 * (ed c a).ε * ((f (a + 6 * (n + (ed c a).k * m)) -
            v.F c (v.Ξ c (a + 6 * (n + (ed c a).k * m)))) / 2 *
            (ec ((ed c a).gam n (τ c a n) m)).re) + (ed c a).ε ^ 2) := by
    refine sum_le_sum fun a _ => ?_
    by_cases ha : regP (v.S c) (v.ρ c / 2) (a - v.n c) = 0
    · simp [ha]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun n _ => ?_) (regP_nonneg _ _)
    by_cases hn : regP (v.S c) (v.ρ0 η θ c) n = 0
    · simp [hn]
    exact mul_le_mul_of_nonneg_left (edata_energy_le hp τ (hE c a) ⟨ha, hn⟩ f hf)
      (regP_nonneg _ _)
  refine h1.trans ?_
  have e2 : ∀ a, ∑ n, regP (v.S c) (v.ρ0 η θ c) n *
      ∑ m, Q a m * (g (a + 6 * (n + (ed c a).k * m)) -
        4 * (ed c a).ε * ((f (a + 6 * (n + (ed c a).k * m)) -
          v.F c (v.Ξ c (a + 6 * (n + (ed c a).k * m)))) / 2 *
          (ec ((ed c a).gam n (τ c a n) m)).re) + (ed c a).ε ^ 2) =
      ∑ n, regP (v.S c) (v.ρ0 η θ c) n * ∑ m, Q a m * g (a + 6 * (n + (ed c a).k * m)) -
        (4 * (ed c a).ε * v.ecorr η θ T f ed τ c a - (ed c a).ε ^ 2) := fun a =>
    split_avg (sum_regP _ hρ00.le) (hQ1 a) _ _ _ _
  simp only [e2, mul_sub, sum_sub_distrib]
  have hg4 : ∀ x, |g x| ≤ 4 := by
    intro x
    have := hv.2.2.2.2.2.1 c (v.Ξ c x)
    obtain ⟨hf0, hf1⟩ := hf x
    rw [abs_le] at this
    rw [hg, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hmix := tv_mix6 (S := v.S c) (n0 := v.n c) hρ0 hρ00
    (mul_nonneg ((Nat.cast_nonneg _).trans (hE c (0 : ZMod p)).2.1) hm0.le) h4K h24
    Q (fun a m => ((ed c a).k : ZMod p) * m)
    (fun a m => regP_nonneg _ _) hQ1 (fun a m hm => by
      have hmb := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hm0.le hm) hm0.le
      have h1 := snorm_nsmul_le (S := v.S c) (ed c a).k m
      have h2 := snorm_mono (hE c a).2.2.2.1 m
      have hk0 : (0 : ℝ) ≤ (ed c a).k := Nat.cast_nonneg _
      calc snorm (v.S c) (((ed c a).k : ZMod p) * m) ≤ (ed c a).k * snorm (ed c a).S m :=
            h1.trans (mul_le_mul_of_nonneg_left h2 hk0)
        _ ≤ K * v.ρm η θ T c :=
            mul_le_mul (hE c a).2.1 hmb (snorm_nonneg _) ((hk0.trans (hE c a).2.1))) g hg4
  rw [← mul_add] at hmix
  have hΦc : (v.ldata c).avg (fun x => (f x - v.F c (v.Ξ c x)) ^ 2) =
      ∑ x, regP (v.S c) (v.ρ c / 2) (x - v.n c) * g x := rfl
  rw [hΦc]
  have := (abs_le.mp hmix).2
  have h4 : 4 * (50 * (v.S c).card * (K * v.ρm η θ T c) / v.ρ0 η θ c +
      50 * (v.S c).card * (6 * v.ρ0 η θ c) / (v.ρ c / 2)) ≤ 4 * E := by linarith
  linarith

end SLA

end

end GT
end File_GT_BadEdB3

section File_GT_BadEdB4
/-!
# Theorem 6.6, the quadratic case: selecting the data

Telescoping `Λ(f) - Λ(𝐟)`, choosing a popular slot and popular labels, the local generalised von
Neumann theorem, and phase alignment.
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- Phase alignment. -/
lemma exists_phase (z : ℂ) : ∃ τ : UnitAddCircle, ec (-τ) * z = (‖z‖ : ℂ) := by
  refine ⟨((Complex.arg z / (2 * Real.pi) : ℝ) : UnitAddCircle), ?_⟩
  rw [← AddCircle.coe_neg, ec_coe]
  have : (2 * Real.pi * -(Complex.arg z / (2 * Real.pi)) : ℝ) = -Complex.arg z := by
    field_simp
  rw [this]
  have hz := Complex.norm_mul_exp_arg_mul_I z
  set a := Complex.arg z
  conv_lhs => rw [← hz]
  rw [mul_comm, mul_assoc, ← Complex.exp_add]
  have h0 : (↑a * Complex.I + Complex.I * ↑(-a) : ℂ) = 0 := by
    push_cast; ring
  rw [h0, Complex.exp_zero, mul_one]

lemma ec_re_neg (x : UnitAddCircle) : (ec (-x)).re = (ec x).re := by
  rw [ec_neg, Complex.conj_re]

namespace SLA

variable (v : SLA p) (η : ℝ) (f : ZMod p → ℝ)

/-- The `i`-th telescoping term of `Λ(f) - Λ(𝐟)` conditioned on the label `c`. -/
def telL (i : Fin 4) (c : v.C) : ℝ :=
  ∑ a, ∑ r, regP (v.S c) (v.ρ c / 2) (a - v.n c) * regP (v.S c) (eps4 η * v.ρ c) r *
    ap4 (telH i f (fun x => v.F c (v.Ξ c x))) a r

variable {v η f}

lemma sum_w_eq (c : v.C) (h : ZMod p → ZMod p → ℝ) :
    ∑ z, (v.triple η).w c z * h z.1 z.2 =
      ∑ a, ∑ r, regP (v.S c) (v.ρ c / 2) (a - v.n c) * regP (v.S c) (eps4 η * v.ρ c) r * h a r := by
  rw [Fintype.sum_prod_type]; rfl

lemma lam_tel (v : SLA p) (η : ℝ) (f : ZMod p → ℝ) :
    (v.triple η).lam f - (v.triple η).lamF = 2 * ∑ i : Fin 4, ∑ c, v.prob c * v.telL η f i c := by
  unfold Triple.lam Triple.lamF
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub, ← sum_sub_distrib]
  have e : ∀ c, ∑ z, ((v.triple η).w c z * (f z.1 * f (z.1 + z.2) * f (z.1 + 2 * z.2) *
      f (z.1 + 3 * z.2)) - (v.triple η).w c z * ((v.triple η).F c z.1 *
      (v.triple η).F c (z.1 + z.2) * (v.triple η).F c (z.1 + 2 * z.2) *
      (v.triple η).F c (z.1 + 3 * z.2))) =
      2 * ∑ i : Fin 4, v.telL η f i c := by
    intro c
    simp_rw [← mul_sub]
    have := sum_w_eq (v := v) (η := η) c (fun a r => f a * f (a + r) * f (a + 2 * r) *
      f (a + 3 * r) - (v.triple η).F c a * (v.triple η).F c (a + r) *
      (v.triple η).F c (a + 2 * r) * (v.triple η).F c (a + 3 * r))
    rw [this]
    unfold telL
    have h2 : ∀ a r, regP (v.S c) (v.ρ c / 2) (a - v.n c) * regP (v.S c) (eps4 η * v.ρ c) r *
        (f a * f (a + r) * f (a + 2 * r) * f (a + 3 * r) - (v.triple η).F c a *
          (v.triple η).F c (a + r) * (v.triple η).F c (a + 2 * r) *
          (v.triple η).F c (a + 3 * r)) =
        ∑ i : Fin 4, 2 * (regP (v.S c) (v.ρ c / 2) (a - v.n c) *
          regP (v.S c) (eps4 η * v.ρ c) r * ap4 (telH i f (fun x => v.F c (v.Ξ c x))) a r) := by
      intro a r
      have h := telescope4 f (fun x => v.F c (v.Ξ c x)) a r
      change _ * (f a * f (a + r) * f (a + 2 * r) * f (a + 3 * r) -
        v.F c (v.Ξ c a) * v.F c (v.Ξ c (a + r)) * v.F c (v.Ξ c (a + 2 * r)) *
          v.F c (v.Ξ c (a + 3 * r))) = _
      rw [h, mul_sum, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    simp only [h2]
    rw [mul_sum]
    simp only [mul_sum]
    rw [sum3_rev]
    exact sum_congr rfl fun i _ => sum_comm
  simp_rw [e, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  refine sum_congr rfl fun c _ => ?_
  change v.prob c * _ = _
  ring

lemma abs_telL_le (hv : v.Valid) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (i : Fin 4) (c : v.C) :
    |v.telL η f i c| ≤ 1 := by
  have hw := (triple_valid hv η).2.2.2.1 c
  have hw0 := (triple_valid hv η).2.2.1 c
  have := abs_wavg_le hw0 hw (fun z => ap4 (telH i f (fun x => v.F c (v.Ξ c x))) z.1 z.2) (B := 1)
    (fun z _ => abs_ap4_le (abs_telH_le (fun x => abs_le.2 ⟨by linarith [(hf x).1], (hf x).2⟩)
      (fun x => hv.2.2.2.2.2.1 c _) i) _ _)
  rw [sum_w_eq] at this
  exact this

/-- A popular slot and popular labels. -/
lemma exists_popular (hη : 0 < η) (hv : v.Valid) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hbad : η < |(v.triple η).lamF - (v.triple η).lam f|) :
    ∃ i : Fin 4, η / 16 ≤ ∑ c, v.prob c * (if η / 16 ≤ |v.telL η f i c| then 1 else 0) := by
  have e := lam_tel v η f
  have hb2 : η / 2 < |∑ i : Fin 4, ∑ c, v.prob c * v.telL η f i c| := by
    rw [abs_sub_comm, e, abs_mul, abs_two] at hbad
    linarith
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, η / 8 ≤ |∑ c, v.prob c * v.telL η f i c| := by
    by_contra h
    push_neg at h
    rw [Fin.sum_univ_four] at hb2
    have := abs_add_le (∑ c, v.prob c * v.telL η f 0 c + ∑ c, v.prob c * v.telL η f 1 c +
      ∑ c, v.prob c * v.telL η f 2 c) (∑ c, v.prob c * v.telL η f 3 c)
    have := abs_add_le (∑ c, v.prob c * v.telL η f 0 c + ∑ c, v.prob c * v.telL η f 1 c)
      (∑ c, v.prob c * v.telL η f 2 c)
    have := abs_add_le (∑ c, v.prob c * v.telL η f 0 c) (∑ c, v.prob c * v.telL η f 1 c)
    linarith [h 0, h 1, h 2, h 3]
  refine ⟨i, ?_⟩
  have hm : η / 8 ≤ ∑ c, v.prob c * |v.telL η f i c| := by
    refine hi.trans ((abs_sum_le_sum_abs _ _).trans (le_of_eq ?_))
    exact sum_congr rfl fun c _ => by rw [abs_mul, abs_of_nonneg (hv.1 c)]
  have := popular hv.1 hv.2.1 (fun c => |v.telL η f i c|) (B := 1) (t := η / 16)
    (by linarith)
    (fun c => abs_telL_le hv hf i c) hm
  linarith

end SLA

end

end GT
end File_GT_BadEdB4

section File_GT_BadEdB5
/-!
# Theorem 6.6, the quadratic case: assembly
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

namespace SLA

variable {v : SLA p} {η : ℝ} {f : ZMod p → ℝ}

/-- The good pairs `(c, a)`: the local `U³` box average of `x ↦ (f - 𝐟)(a + 6x)/2` is large. -/
def edGood (v : SLA p) (η : ℝ) (f : ZMod p → ℝ) (i : Fin 4) (θ : ℝ) (c : v.C) (a : ZMod p) :
    Prop :=
  (η / 16 / 4) ^ 8 ≤ box3 (regP (v.S c) (v.ρ0 η θ c)) (regP (v.S c) (θ * v.ρ0 η θ c))
    (regP (v.S c) (θ ^ 2 * v.ρ0 η θ c)) (fun x => telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * x))

instance (v : SLA p) (η : ℝ) (f : ZMod p → ℝ) (i : Fin 4) (θ : ℝ) (c : v.C) (a : ZMod p) :
    Decidable (v.edGood η f i θ c a) := by
  unfold edGood; infer_instance

lemma good_mass (hη0 : 0 < η) (hv : v.Valid) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {i : Fin 4}
    (hi : η / 16 ≤ ∑ c, v.prob c * (if η / 16 ≤ |v.telL η f i c| then 1 else 0)) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hnum : ∀ c, 12 * (eps4 η * v.ρ c) ≤ v.ρ c / 2 ∧
      50 * ((v.S c).card : ℝ) * (3 * (eps4 η * v.ρ c)) / (v.ρ c / 2) ≤ η / 16 / 8 ∧
      72 * v.ρ0 η θ c ≤ v.ρ c / 2 ∧
      50 * ((v.S c).card : ℝ) * (18 * v.ρ0 η θ c) / (v.ρ c / 2) ≤ η / 16 / 16 ∧
      72 * v.ρ0 η θ c ≤ eps4 η * v.ρ c ∧
      50 * ((v.S c).card : ℝ) * (18 * v.ρ0 η θ c) / (eps4 η * v.ρ c) ≤ η / 16 / 16) :
    η / 16 / 4 * (η / 16) ≤ ∑ c, v.prob c * ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
      (if v.edGood η f i θ c a then 1 else 0) := by
  classical
  have hc : ∀ c, η / 16 / 4 * (if η / 16 ≤ |v.telL η f i c| then 1 else 0) ≤
      ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) * (if v.edGood η f i θ c a then 1 else 0) := by
    intro c
    by_cases hpop : η / 16 ≤ |v.telL η f i c|
    · rw [if_pos hpop, mul_one]
      have hρ := (hv.2.2.2.1 c).1
      obtain ⟨h1, h1', h2, h2', h3, h3'⟩ := hnum c
      have := vn_core (S := v.S c) (n0 := v.n c) (ρa := v.ρ c / 2) (ρr := eps4 η * v.ρ c)
        (ρA := v.ρ0 η θ c) (θ := θ) (δ := η / 16) (by positivity)
        (by unfold eps4; positivity) (ρ0_pos hv hθ0 c) hθ0 hθ1 (by positivity) i
        (telH i f (fun y => v.F c (v.Ξ c y)))
        (abs_telH_le (fun x => abs_le.2 ⟨by linarith [(hf x).1], (hf x).2⟩)
          (fun x => hv.2.2.2.2.2.1 c _) i) hpop h1 h1' h2 h2' h3 h3'
      exact this
    · rw [if_neg hpop, mul_zero]
      exact sum_nonneg fun a _ => mul_nonneg (regP_nonneg _ _) (by split_ifs <;> norm_num)
  calc η / 16 / 4 * (η / 16) ≤ η / 16 / 4 * ∑ c, v.prob c *
        (if η / 16 ≤ |v.telL η f i c| then 1 else 0) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ = ∑ c, v.prob c * (η / 16 / 4 * (if η / 16 ≤ |v.telL η f i c| then 1 else 0)) := by
        rw [mul_sum]; exact sum_congr rfl fun c _ => by ring
    _ ≤ _ := sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hc c) (hv.1 c)

/-- The correlation of a good pair after phase alignment. -/
lemma ecorr_eq {θ : ℝ} {T : ℕ} (ed : v.C → ZMod p → EDat p)
    (τ : v.C → ZMod p → ZMod p → UnitAddCircle) (i : Fin 4) (c : v.C) (a : ZMod p)
    (hτ : ∀ n, ec (-τ c a n) * (∑ m, (regP (ed c a).S (v.ρm η θ T c) m : ℂ) *
      (((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * (n + (ed c a).k * m)) : ℝ) : ℂ) *
        ec (-((ed c a).φ m) - ZMod.toAddCircle ((ed c a).β n * m)))) =
      (‖∑ m, (regP (ed c a).S (v.ρm η θ T c) m : ℂ) *
      (((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * (n + (ed c a).k * m)) : ℝ) : ℂ) *
        ec (-((ed c a).φ m) - ZMod.toAddCircle ((ed c a).β n * m)))‖ : ℂ)) :
    v.ecorr η θ T f ed τ c a = ∑ n, regP (v.S c) (v.ρ0 η θ c) n *
      ‖∑ m, (regP (ed c a).S (v.ρm η θ T c) m : ℂ) *
      (((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * (n + (ed c a).k * m)) : ℝ) : ℂ) *
        ec (-((ed c a).φ m) - ZMod.toAddCircle ((ed c a).β n * m)))‖ := by
  unfold ecorr
  refine sum_congr rfl fun n _ => ?_
  congr 1
  have h := congrArg Complex.re (hτ n)
  rw [Complex.ofReal_re] at h
  rw [← h, mul_sum, Complex.re_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [telH_self]
  set D := (f (a + 6 * (n + (ed c a).k * m)) -
    v.F c (v.Ξ c (a + 6 * (n + (ed c a).k * m)))) / 2
  have e1 : ec (-τ c a n) * ((regP (ed c a).S (v.ρm η θ T c) m : ℂ) * ((D : ℂ) *
      ec (-((ed c a).φ m) - ZMod.toAddCircle ((ed c a).β n * m)))) =
      ((regP (ed c a).S (v.ρm η θ T c) m * D : ℝ) : ℂ) *
        ec (-((ed c a).gam n (τ c a n) m)) := by
    unfold EDat.gam
    rw [show -((ed c a).φ m + ZMod.toAddCircle ((ed c a).β n * m) + τ c a n) =
      (-((ed c a).φ m) - ZMod.toAddCircle ((ed c a).β n * m)) + -τ c a n by abel, ec_add]
    push_cast; ring
  rw [e1, Complex.re_ofReal_mul, ec_re_neg]
  ring

set_option maxHeartbeats 4000000 in
/-- **Theorem 6.6, second case** (a bad four-term count). -/
theorem bad_ed_quad (hp : p.Prime) (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
    (hpη : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hv : v.Valid) (hb : v.Bounds η)
    (hbad : η < |(v.triple η).lamF - (v.triple η).lam f|) :
    ∃ v' : SLA p, v'.Valid ∧ v.Edge η f v' ∧
      (v'.triple η).energy f ≤ (v.triple η).energy f - η ^ C2 := by
  classical
  haveI := Fact.mk hp
  haveI := nonempty_C hv
  obtain ⟨i, hi⟩ := exists_popular hη0 hv hf hbad
  set s := v.d1 with hs_def
  set θ := edθ s η with hθ_def
  set T := edT η with hT_def
  set K := edK s η with hK_def
  set κ := edκ η with hκ_def
  set E := edE η with hE_def
  have hcs : ∀ c, (v.S c).card ≤ s := fun c =>
    Finset.le_sup (f := fun c => (v.S c).card) (mem_univ c)
  have hρc : ∀ c, Real.exp (-(1 / η) ^ (2 * C5)) ≤ v.ρ c := fun c => by
    refine hb.2.2.1.trans ?_
    unfold SLA.rmin; exact ciInf_le (Finite.bddBelow_range _) c
  have hN : ∀ c, EdNum η s (v.S c).card v.d2 (v.ρ c) p := fun c =>
    ed_num hη0 hη1 (hcs c) hb.1 hb.2.1 (hρc c) (hv.2.2.2.1 c).2 hpη
  obtain ⟨c0⟩ := (inferInstance : Nonempty v.C)
  have h0 := hN c0
  have hθ0 : 0 < θ := h0.θpos
  have hθ1 : θ ≤ 1 := h0.θle
  have hK1 : 1 ≤ K := h0.K1
  have hkp : 6 * K < p := h0.kp
  have hκ0 : 0 ≤ κ := h0.κ0
  have hκ1 : κ ≤ 1 / 4 := h0.κ1
  have hJ0 : 0 ≤ u3J (edηi η) := h0.J0
  have hp6 : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ K → ((6 * k : ℕ) : ZMod p) ≠ 0 := by
    intro k hk1 hkK
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h6 : 0 < 6 * k := by omega
    have := Nat.le_of_dvd h6 hdvd
    have : (p : ℝ) ≤ 6 * k := by exact_mod_cast this
    push_cast at this
    linarith
  -- the inverse theorem at a good pair
  have key : ∀ c a, v.edGood η f i θ c a → ∃ e : EDat p, v.EProp η θ T K c e ∧ e.ε = κ ∧
      ((e.S.card : ℝ) ≤ (v.S c).card + u3J (edηi η)) ∧
      κ ≤ ∑ n, regP (v.S c) (v.ρ0 η θ c) n * ‖∑ m, (regP e.S (v.ρm η θ T c) m : ℂ) *
        (((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * (n + e.k * m)) : ℝ) : ℂ) *
          ec (-(e.φ m) - ZMod.toAddCircle (e.β n * m)))‖ := by
    intro c a hg
    have hNc := hN c
    have hH : ∀ x, |telH i f (fun y => v.F c (v.Ξ c y)) i x| ≤ 1 :=
      abs_telH_le (fun x => abs_le.2 ⟨by linarith [(hf x).1], (hf x).2⟩)
        (fun x => hv.2.2.2.2.2.1 c _) i i
    have hU : edηi η ≤ ‖u3avg (v.S c) (v.ρ0 η θ c) (θ * v.ρ0 η θ c) (θ ^ 2 * v.ρ0 η θ c)
        (fun x => ((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * x) : ℝ) : ℂ))‖ := by
      rw [u3avg_ofReal, Complex.norm_real, Real.norm_eq_abs]
      exact le_trans hg (le_abs_self _)
    obtain ⟨k, S', φ, β, hk1, hkK, hSS, hScard, hφ, hcorr⟩ := inv_u3 hp (hv.2.2.1 c) (hcs c)
      hNc.ηipos hNc.ηile hNc.ρ0pos hNc.ρ0le hθ0 le_rfl hNc.pl
      (fun x => ((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * x) : ℝ) : ℂ))
      (fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hH _) hU
    exact ⟨⟨k, S', φ, β, κ⟩, ⟨hk1, hkK, hp6 k hk1 hkK, hSS, hκ0, hκ1, hφ⟩, rfl, hScard, hcorr⟩
  -- the trivial data at a bad pair
  have triv : ∀ c, v.EProp η θ T K c ⟨1, v.S c, 0, 0, 0⟩ := fun c =>
    ⟨le_rfl, by simpa using hK1, hp6 1 le_rfl (by simpa using hK1), subset_rfl, le_rfl,
      by norm_num, LocQuad.const' _ _⟩
  set ed : v.C → ZMod p → EDat p := fun c a =>
    if hg : v.edGood η f i θ c a then (key c a hg).choose else ⟨1, v.S c, 0, 0, 0⟩ with hed
  have hE : ∀ c a, v.EProp η θ T K c (ed c a) := by
    intro c a
    by_cases hg : v.edGood η f i θ c a
    · simp only [hed, dif_pos hg]; exact (key c a hg).choose_spec.1
    · simp only [hed, dif_neg hg]; exact triv c
  have hEcard : ∀ c a, ((ed c a).S.card : ℝ) ≤ (v.S c).card + u3J (edηi η) := by
    intro c a
    by_cases hg : v.edGood η f i θ c a
    · simp only [hed, dif_pos hg]; exact (key c a hg).choose_spec.2.2.1
    · simp only [hed, dif_neg hg]; linarith
  set τ : v.C → ZMod p → ZMod p → UnitAddCircle := fun c a n =>
    (exists_phase (∑ m, (regP (ed c a).S (v.ρm η θ T c) m : ℂ) *
      (((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * (n + (ed c a).k * m)) : ℝ) : ℂ) *
        ec (-((ed c a).φ m) - ZMod.toAddCircle ((ed c a).β n * m))))).choose with hτ
  have hτs : ∀ c a n, ec (-τ c a n) * (∑ m, (regP (ed c a).S (v.ρm η θ T c) m : ℂ) *
      (((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * (n + (ed c a).k * m)) : ℝ) : ℂ) *
        ec (-((ed c a).φ m) - ZMod.toAddCircle ((ed c a).β n * m)))) =
      (‖∑ m, (regP (ed c a).S (v.ρm η θ T c) m : ℂ) *
      (((telH i f (fun y => v.F c (v.Ξ c y)) i (a + 6 * (n + (ed c a).k * m)) : ℝ) : ℂ) *
        ec (-((ed c a).φ m) - ZMod.toAddCircle ((ed c a).β n * m)))‖ : ℂ) := fun c a n =>
    (exists_phase _).choose_spec
  have hNum : ∀ c, v.ENum η θ T K E c := by
    intro c
    have hNc := hN c
    exact ⟨hθ0, hNc.e0, hNc.e1, hNc.e2, hNc.e3, hNc.e4, hNc.e5⟩
  -- the gain at each pair
  have hgain : ∀ c a, 3 * κ ^ 2 * (if v.edGood η f i θ c a then 1 else 0) ≤
      4 * (ed c a).ε * v.ecorr η θ T f ed τ c a - (ed c a).ε ^ 2 := by
    intro c a
    by_cases hg : v.edGood η f i θ c a
    · rw [if_pos hg, mul_one]
      have hspec := (key c a hg).choose_spec
      have hε : (ed c a).ε = κ := by simp only [hed, dif_pos hg]; exact hspec.2.1
      have hcor : κ ≤ v.ecorr η θ T f ed τ c a := by
        rw [ecorr_eq ed τ i c a (hτs c a)]
        have := hspec.2.2.2
        simp only [hed, dif_pos hg]
        exact this
      rw [hε]
      nlinarith
    · rw [if_neg hg, mul_zero]
      have hε : (ed c a).ε = 0 := by simp only [hed, dif_neg hg]
      rw [hε]; ring_nf; exact le_refl _
  have hmass := good_mass hη0 hv hf hi hθ0 hθ1 (fun c => by
    have hNc := hN c
    exact ⟨hNc.n1, hNc.n2, hNc.n3, hNc.n4, hNc.n5, hNc.n6⟩)
  have hen := energy_enew hp hv τ hθ0 hE hNum f hf
  have hsum : 3 * κ ^ 2 * (η / 16 / 4 * (η / 16)) ≤ ∑ c, v.prob c *
      ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
        (4 * (ed c a).ε * v.ecorr η θ T f ed τ c a - (ed c a).ε ^ 2) := by
    calc 3 * κ ^ 2 * (η / 16 / 4 * (η / 16)) ≤ 3 * κ ^ 2 * ∑ c, v.prob c *
          ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
            (if v.edGood η f i θ c a then 1 else 0) :=
          mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num) (sq_nonneg κ))
      _ = ∑ c, v.prob c * ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
            (3 * κ ^ 2 * (if v.edGood η f i θ c a then 1 else 0)) := by
          rw [mul_sum]; refine sum_congr rfl fun c _ => ?_
          rw [mul_sum, mul_sum, mul_sum]; exact sum_congr rfl fun a _ => by ring
      _ ≤ _ := sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hgain c a) (regP_nonneg _ _)) (hv.1 c)
  refine ⟨v.enew η θ T ed τ, enew_valid hp hv τ hθ0 hE hNum, ⟨?_, d2_enew ed τ, ?_, ?_, ?_⟩, ?_⟩
  · refine (d1_enew ed τ hJ0 hEcard).trans ?_
    have := h0.J1
    change (s : ℝ) + u3J (edηi η) ≤ s + (1 / η) ^ C2
    linarith
  · exact rmin_enew hv ed τ (Real.exp_pos _).le (fun c => (hN c).rm)
  · refine (volm_enew hv ed τ).trans ?_
    exact mul_le_mul_of_nonneg_right h0.vol (volm_nonneg v)
  · have hx := ex_enew hp hv τ hθ0 hE hNum f (B := 1)
      (fun x => abs_le.2 ⟨by linarith [(hf x).1], (hf x).2⟩)
    unfold SLA.waste
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [show (v.triple η).ex f - ∑ x, f x / p - (((v.enew η θ T ed τ).triple η).ex f -
      ∑ x, f x / p) = -(((v.enew η θ T ed τ).triple η).ex f - (v.triple η).ex f) by ring,
      abs_neg]
    linarith [h0.E1]
  · have := h0.dec
    linarith

end SLA

end

end GT
end File_GT_BadEdB5

section File_GT_BadEd
/-!
# Theorem 6.6: a bad approximation implies an energy decrement
-/

open Finset KM

namespace GT

noncomputable section

/-- **Theorem 6.6** (bad approximation implies energy decrement). -/
theorem bad_ed_thm {p : ℕ} [NeZero p] (hp : p.Prime) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
    (hpη : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) {f : ZMod p → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {v : SLA p} (hv : v.Valid) (hb : v.Bounds η)
    (hbad : η < |(v.triple η).exF - (v.triple η).ex f| ∨
      η < |(v.triple η).lamF - (v.triple η).lam f|) :
    ∃ v' : SLA p, v'.Valid ∧ v.Edge η f v' ∧
      (v'.triple η).energy f ≤ (v.triple η).energy f - η ^ C2 := by
  rcases hbad with h | h
  · exact SLA.bad_ed_lin hv hη0 hη1 hf h
  · exact SLA.bad_ed_quad hp hη0 hη1 hpη hf hv hb h

end

end GT
end File_GT_BadEd

open Finset KM
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
    (hpη : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) {f : ZMod p → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {v : SLA p} (hv : v.Valid) (hb : v.Bounds η)
    (hbad : η < |(v.triple η).exF - (v.triple η).ex f| ∨
      η < |(v.triple η).lamF - (v.triple η).lam f|) :
    ∃ v' : SLA p, v'.Valid ∧ v.Edge η f v' ∧
      (v'.triple η).energy f ≤ (v.triple η).energy f - η ^ C2 :=
  @GT.bad_ed_thm p _ hp η hη0 hη1 hpη f hf v hv hb hbad

