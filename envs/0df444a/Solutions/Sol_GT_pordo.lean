-- Prove2me | solution 1 for GT.pordo
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:55:29.40626+00:00
-- url     : https://prove2.me/submissions/dfd4e76f-d45b-4ced-a863-d2246203d164

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

@[simp] lemma neg_mem_bohr_iff : -x ∈ bohr Γ ρ ↔ x ∈ bohr Γ ρ :=
  ⟨fun h => by simpa using neg_mem_bohr h, neg_mem_bohr⟩

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

@[simp] lemma mu_apply : mu S x = if x ∈ S then (S.card : ℝ)⁻¹ else 0 := rfl

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

@[simp] lemma snorm_neg (h : ZMod N) : snorm S (-h) = snorm S h := by
  unfold snorm; simp [mul_neg, cn_neg]

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

lemma regP_neg (Γ : Finset (ZMod p)) (ρ : ℝ) (a : ZMod p) : regP Γ ρ (-a) = regP Γ ρ a := by
  unfold regP
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [mu_apply, neg_mem_bohr_iff]

lemma sum_regP_neg_real (Γ : Finset (ZMod p)) (ρ : ℝ) (F : ZMod p → ℝ) :
    ∑ x, regP Γ ρ x * F (-x) = ∑ x, regP Γ ρ x * F x :=
  Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => by simp [regP_neg])

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

end Good

/-! ### Box Cauchy–Schwarz -/

section box

variable {α β : Type*} [Fintype α] [Fintype β]

end box

/-! ### Translations of centred regular variables -/

end

end GT
end File_GT_U3Base

section File_GT_U3S1
/-!
# Local inverse `U³`, first step: a frequency for each popular derivative

(Green–Tao, Theorem 9.1.)
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma sum4_swap {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M] (F : α → α → α → α → M) :
    ∑ c, ∑ d, ∑ e, ∑ g, F c d e g = ∑ e, ∑ g, ∑ c, ∑ d, F c d e g := by
  calc ∑ c, ∑ d, ∑ e, ∑ g, F c d e g = ∑ c, ∑ e, ∑ d, ∑ g, F c d e g :=
        sum_congr rfl fun c _ => sum_comm
    _ = ∑ e, ∑ c, ∑ d, ∑ g, F c d e g := sum_comm
    _ = ∑ e, ∑ c, ∑ g, ∑ d, F c d e g :=
        sum_congr rfl fun e _ => sum_congr rfl fun c _ => sum_comm
    _ = ∑ e, ∑ g, ∑ c, ∑ d, F c d e g := sum_congr rfl fun e _ => sum_comm

end

end GT
end File_GT_U3S1

section File_GT_U3Q
/-!
# Centred random additive quadruples

(Green–Tao, Corollary 9.3.)  A random additive quadruple centred at `c` with frequencies `T`
and scales `r2 ≤ r3 ≤ r4` is `qd c x2 x3 x4` with `x2, x3, x4` drawn independently and
regularly from `B(T, r2)`, `B(T, r3)`, `B(T, r4)`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### A general translation estimate inside a context -/

lemma snorm_le_of_regP_ne {Γ : Finset (ZMod p)} {ρ : ℝ} (hρ : 0 ≤ ρ) {x : ZMod p}
    (hx : regP Γ ρ x ≠ 0) : snorm Γ x ≤ ρ :=
  snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ hx) hρ

end

end GT
end File_GT_U3Q

section File_GT_U3S4b
/-!
# Local inverse `U³`, fourth step: a large local `U²` norm gives an energy increment

This is the estimate (bb) in the proof of Green–Tao, Theorem 9.5.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma sum_regP_center_shift (T : Finset (ZMod p)) (ρ : ℝ) (a : ZMod p) (F : ZMod p → ℝ) :
    ∑ u, regP T ρ (u - a) * F u = ∑ v, regP T ρ v * F (a + v) :=
  (Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun v => by simp)).symm

end

end GT
end File_GT_U3S4b

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

lemma ratio_le_sc (K : ℝ) (hK : 0 ≤ K) {m n : ℕ} (h : m < n) : K * R n / R m ≤ K * θ := by
  rw [div_le_iff₀ (hR0 m), mul_assoc]
  exact mul_le_mul_of_nonneg_left (R_lt_le hR0 hRθ hθ0 hθ1 h) hK

lemma four_R_le {m n : ℕ} (h : m < n) (hθ : θ ≤ 1 / 16) : 4 * R n ≤ R m := by
  have := R_lt_le hR0 hRθ hθ0 hθ1 h
  nlinarith [hR0 m]

lemma four_R2_le {m n n' : ℕ} (h : m < n) (h' : m < n') (hθ : θ ≤ 1 / 16) :
    4 * (R n + R n') ≤ R m := by
  have := R_lt_le hR0 hRθ hθ0 hθ1 h
  have := R_lt_le hR0 hRθ hθ0 hθ1 h'
  nlinarith [hR0 m]

end scales

/-! ### Neighbourhoods -/

lemma lvl_le (i : Fin 4) : lvl i ≤ 2 := by fin_cases i <;> decide

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

lemma abs_bal_le {R : ℕ → ℝ} (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) (hR : 0 ≤ R (j + lvl i)) (u : ZMod p) :
    |bal R A T c j i u| ≤ 1 := by
  unfold bal
  have := alph_nonneg R A T c j i
  have := alph_le_one A T c j i hR
  have := ind_nonneg (A i) u
  have := ind_le_one (A i) u
  rw [abs_le]; constructor <;> linarith

section refine

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16)
include hR0 hRk hθ0 hθ1

end refine

end

end GT
end File_GT_U3S4d

section File_GT_U3S4e
/-!
# Local inverse `U³`, fourth step: the score maximisation (Green–Tao, Theorem 9.5)

We maximise the score over all neighbourhoods `(c, 20k, T)` with `S ⊆ T`, `|T| ≤ |S| + k`,
`k < K`.  At a maximiser the weighted average of `W` is still large, and every balanced
function `1_{A_i} - α_i` has a small local `U²` norm: otherwise the random refinement would
increase the score on average.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

section avg33

variable (T : Finset (ZMod p)) (r2 r3 r4 s2 s3 s4 : ℝ)

variable {r2 r3 r4 s2 s3 s4} (hr2 : 0 ≤ r2) (hr3 : 0 ≤ r3) (hr4 : 0 ≤ r4) (hs2 : 0 ≤ s2)
  (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4)
include hr2 hr3 hr4 hs2 hs3 hs4

end avg33

section refine

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16)
include hR0 hRk hθ0 hθ1

lemma ratio_sum2 {a b d : ℕ} (hab : d < a) (hbd : d < b) :
    (R a + R b) / R d ≤ 2 * θ := by
  have hθ1' : θ ≤ 1 := by linarith
  have := R_lt_le hR0 hRk hθ0 hθ1' hab
  have := R_lt_le hR0 hRk hθ0 hθ1' hbd
  rw [div_le_iff₀ (hR0 d)]; linarith

end refine

end

end GT
end File_GT_U3S4e

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

lemma sq_sub_sq_le_of_abs {X Z e : ℝ} (hX : |X| ≤ 1) (hZ : |Z| ≤ 1) (h : |X - Z| ≤ e) :
    X ^ 2 ≤ Z ^ 2 + 2 * e := by
  have h1 : X ^ 2 - Z ^ 2 = (X - Z) * (X + Z) := by ring
  have h2 : |X + Z| ≤ 2 := (abs_add_le X Z).trans (by linarith)
  have h3 : (X - Z) * (X + Z) ≤ |X - Z| * |X + Z| := by rw [← abs_mul]; exact le_abs_self _
  have h4 : |X - Z| * |X + Z| ≤ e * 2 := mul_le_mul h h2 (abs_nonneg _) ((abs_nonneg _).trans h)
  linarith

lemma wavg_add_const {α : Type*} [Fintype α] {P : α → ℝ} (hP1 : ∑ x, P x = 1) (A : α → ℝ)
    (b : ℝ) : ∑ x, P x * (A x + b) = ∑ x, P x * A x + b := by
  simp only [mul_add, sum_add_distrib, ← sum_mul, hP1, one_mul]

lemma U2f_eq_sq (T : Finset (ZMod p)) (ρ0 ρ1 : ℝ) (g : ZMod p → ℝ) (u : ZMod p) :
    U2f T ρ0 ρ1 g u = ∑ h1, ∑ h1', regP T ρ1 h1 * regP T ρ1 h1' *
      (∑ h0, regP T ρ0 h0 * (g (u + h0 + h1) * g (u + h0 + h1'))) ^ 2 := by
  unfold U2f
  symm
  simp only [sq, sum_mul, mul_sum]
  rw [sum4_swap]
  refine sum_congr rfl fun h0 _ => sum_congr rfl fun h0' _ => sum_congr rfl fun h1 _ =>
    sum_congr rfl fun h1' _ => ?_
  ring

/-- **Estimate (po)** of Lemma 9.6. -/
theorem wmix_po {T : Finset (ZMod p)} {rl rm r10 r11 ε : ℝ} (hrl : 0 < rl) (hrm : 0 < rm)
    (hr10 : 0 < r10) (hr11 : 0 < r11) (h4m : 4 * r11 ≤ rm) (h4l : 4 * (rm + r10) ≤ rl)
    (f G : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hG : ∀ x, |G x| ≤ 1) (c : ZMod p)
    (hU : ∑ u, regP T rl (u - c) * U2f T r10 r11 f u ≤ ε) :
    ∑ n, regP T rl (n - c) * (∑ k, regP T rm k * (f (n - k) * G k)) ^ 2 ≤
      √ε + 50 * T.card * (rm + r10) / rl + 2 * (50 * T.card * r11 / rm) := by
  set e1 := 50 * T.card * r11 / rm with he1
  set e2 := 50 * T.card * (rm + r10) / rl with he2
  have hPn := regP_center_isDist T hrl.le c
  have hPk := regP_isDist T hrm.le
  have hP1 := regP_isDist T hr11.le
  have hP0 := regP_isDist T hr10.le
  have hfG : ∀ x y, |f x * G y| ≤ 1 := fun x y => by
    rw [abs_mul]; exact mul_le_one₀ (hf x) (abs_nonneg _) (hG y)
  set X : ZMod p → ℝ := fun n => ∑ k, regP T rm k * (f (n - k) * G k) with hX
  set Y : ZMod p → ZMod p → ℝ := fun n k => ∑ h1, regP T r11 h1 * (f (n - k + h1) * G (k - h1))
    with hY
  have hXb : ∀ n, |X n| ≤ 1 := fun n => abs_wavg_le hPk.1 hPk.2 _ fun k _ => hfG _ _
  have hYb : ∀ n k, |Y n k| ≤ 1 := fun n k => abs_wavg_le hP1.1 hP1.2 _ fun h1 _ => hfG _ _
  -- A
  have hA : ∀ n, |X n - ∑ k, regP T rm k * Y n k| ≤ e1 := by
    intro n
    have e : ∑ k, regP T rm k * Y n k =
        ∑ h1, regP T r11 h1 * ∑ k, regP T rm k * (f (n - (k + -h1)) * G (k + -h1)) := by
      simp only [hY, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun h1 _ => sum_congr rfl fun k _ => ?_
      rw [show n - (k + -h1) = n - k + h1 by ring, show k + -h1 = k - h1 by ring]
      ring
    rw [e, abs_sub_comm]
    have e' : ∑ h1, regP T r11 h1 * ∑ k, regP T rm k * (f (n - (k + -h1)) * G (k + -h1)) - X n =
        ∑ h1, regP T r11 h1 * (∑ k, regP T rm k * (f (n - (k + -h1)) * G (k + -h1)) -
          ∑ k, regP T rm k * (f (n - k) * G k)) := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP1.2, one_mul, hX]
    rw [e']
    refine abs_wavg_le hP1.1 hP1.2 _ fun h1 hh1 => ?_
    have hs : snorm T (-h1) ≤ r11 := by rw [snorm_neg]; exact snorm_le_of_regP_ne hr11.le hh1
    have := shift_real subset_rfl hrm h4m hs (fun k => f (n - k) * G k) (fun k => hfG _ _)
    rw [one_mul] at this
    exact this
  -- B, C
  have hBC : ∀ n, X n ^ 2 ≤ ∑ k, regP T rm k * (Y n k) ^ 2 + 2 * e1 := by
    intro n
    have hZ : |∑ k, regP T rm k * Y n k| ≤ 1 := abs_wavg_le hPk.1 hPk.2 _ fun k _ => hYb _ _
    have h1 := sq_sub_sq_le_of_abs (hXb n) hZ (hA n)
    have h2 := sq_wavg_le (fun k => Y n k) hPk.1 hPk.2
    linarith
  -- D
  set M : ZMod p → ZMod p → ZMod p → ℝ := fun n h1 h1' =>
    ∑ h0, regP T r10 h0 * (f (n + h0 + h1) * f (n + h0 + h1')) with hM
  have hD : ∀ k, regP T rm k ≠ 0 →
      ∑ n, regP T rl (n - c) * (Y n k) ^ 2 ≤ √ε + e2 := by
    intro k hk
    have hsk : snorm T k ≤ rm := snorm_le_of_regP_ne hrm.le hk
    set V : ZMod p → ℝ := fun v => (∑ h1, regP T r11 h1 * (f (v + h1) * G (k - h1))) ^ 2
      with hV
    have hVb : ∀ v, |V v| ≤ 1 := fun v => by
      have := abs_wavg_le hP1.1 hP1.2 (fun h1 => f (v + h1) * G (k - h1)) fun h1 _ => hfG _ _
      rw [hV, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (∑ h1, regP T r11 h1 * (f (v + h1) * G (k - h1))),
        sq_abs (∑ h1, regP T r11 h1 * (f (v + h1) * G (k - h1)))]
    have hYV : ∀ n, (Y n k) ^ 2 = V (n + -k) := fun n => by
      simp only [hY, hV, sub_eq_add_neg]
    simp_rw [hYV]
    have D1 := shift_real_c subset_rfl hrl (by linarith : 4 * rm ≤ rl)
      (by rw [snorm_neg]; exact hsk) c V hVb
    have D2 : ∀ h0, regP T r10 h0 ≠ 0 →
        |∑ n, regP T rl (n - c) * V (n + h0) - ∑ n, regP T rl (n - c) * V n| ≤
          50 * T.card * r10 / rl := fun h0 hh0 => by
      have := shift_real_c subset_rfl hrl (by linarith : 4 * r10 ≤ rl)
        (snorm_le_of_regP_ne hr10.le hh0) c V hVb
      rwa [one_mul] at this
    rw [one_mul] at D1
    have D2' : ∑ n, regP T rl (n - c) * V n ≤
        ∑ h0, regP T r10 h0 * ∑ n, regP T rl (n - c) * V (n + h0) + 50 * T.card * r10 / rl := by
      have : ∑ h0, regP T r10 h0 * (∑ n, regP T rl (n - c) * V n -
          ∑ n, regP T rl (n - c) * V (n + h0)) ≤ 50 * T.card * r10 / rl :=
        wavg_le hP0.1 hP0.2 _ fun h0 hh0 => by
          have := D2 h0 hh0; rw [abs_sub_comm] at this; exact (le_abs_self _).trans this
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP0.2, one_mul] at this
      linarith
    -- D3
    have D3 : ∀ n, ∑ h0, regP T r10 h0 * V (n + h0) ≤
        ∑ h1, ∑ h1', regP T r11 h1 * regP T r11 h1' * |M n h1 h1'| := by
      intro n
      have e : ∑ h0, regP T r10 h0 * V (n + h0) = ∑ h1, ∑ h1', regP T r11 h1 * regP T r11 h1' *
          (G (k - h1) * G (k - h1') * M n h1 h1') := by
        simp only [hV, hM, sq, sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun h1 _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun h1' _ => sum_congr rfl fun h0 _ => ?_
        ring
      rw [e]
      refine sum_le_sum fun h1 _ => sum_le_sum fun h1' _ => ?_
      have hw : 0 ≤ regP T r11 h1 * regP T r11 h1' := mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)
      refine mul_le_mul_of_nonneg_left ?_ hw
      calc G (k - h1) * G (k - h1') * M n h1 h1' ≤ |G (k - h1) * G (k - h1') * M n h1 h1'| :=
            le_abs_self _
        _ = |G (k - h1)| * |G (k - h1')| * |M n h1 h1'| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * 1 * |M n h1 h1'| := by
            gcongr
            · exact hG _
            · exact hG _
        _ = |M n h1 h1'| := by ring
    -- D4: Jensen
    have D4 : (∑ n, regP T rl (n - c) *
        (∑ h1, ∑ h1', regP T r11 h1 * regP T r11 h1' * |M n h1 h1'|)) ^ 2 ≤
        ∑ n, regP T rl (n - c) * U2f T r10 r11 f n := by
      refine (sq_wavg_le _ hPn.1 hPn.2).trans (sum_le_sum fun n _ => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hPn.1 n)
      rw [U2f_eq_sq]
      have e : ∀ h1, ∑ h1', regP T r11 h1 * regP T r11 h1' * |M n h1 h1'| =
          regP T r11 h1 * ∑ h1', regP T r11 h1' * |M n h1 h1'| := fun h1 => by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      have e2 : ∀ h1, ∑ h1', regP T r11 h1 * regP T r11 h1' *
          (∑ h0, regP T r10 h0 * (f (n + h0 + h1) * f (n + h0 + h1'))) ^ 2 =
          regP T r11 h1 * ∑ h1', regP T r11 h1' * (M n h1 h1') ^ 2 := fun h1 => by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      simp_rw [e, e2]
      refine (sq_wavg_le _ hP1.1 hP1.2).trans (sum_le_sum fun h1 _ => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hP1.1 h1)
      have := sq_wavg_le (fun h1' => |M n h1 h1'|) hP1.1 hP1.2
      simpa only [sq_abs] using this
    have hU0 : 0 ≤ ∑ n, regP T rl (n - c) *
        (∑ h1, ∑ h1', regP T r11 h1 * regP T r11 h1' * |M n h1 h1'|) :=
      sum_nonneg fun n _ => mul_nonneg (hPn.1 n) (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
        mul_nonneg (mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)) (abs_nonneg _))
    have D5 : ∑ n, regP T rl (n - c) *
        (∑ h1, ∑ h1', regP T r11 h1 * regP T r11 h1' * |M n h1 h1'|) ≤ √ε := by
      rw [← Real.sqrt_sq hU0]
      exact Real.sqrt_le_sqrt (D4.trans hU)
    -- assemble
    have D6 : ∑ h0, regP T r10 h0 * ∑ n, regP T rl (n - c) * V (n + h0) ≤ √ε := by
      have e : ∑ h0, regP T r10 h0 * ∑ n, regP T rl (n - c) * V (n + h0) =
          ∑ n, regP T rl (n - c) * ∑ h0, regP T r10 h0 * V (n + h0) := by
        simp only [mul_sum]; rw [sum_comm]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      rw [e]
      refine le_trans ?_ D5
      exact sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (D3 n) (hPn.1 n)
    have := (abs_le.1 D1).2
    have he2' : e2 = 50 * T.card * rm / rl + 50 * T.card * r10 / rl := by
      rw [he2]; ring
    linarith
  -- final
  clear_value X Y M
  have F1 : ∑ n, regP T rl (n - c) * (X n) ^ 2 ≤
      ∑ n, regP T rl (n - c) * (∑ k, regP T rm k * (Y n k) ^ 2 + 2 * e1) :=
    sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hBC n) (hPn.1 n)
  have F2 : ∑ n, regP T rl (n - c) * (∑ k, regP T rm k * (Y n k) ^ 2 + 2 * e1) =
      ∑ n, regP T rl (n - c) * (∑ k, regP T rm k * (Y n k) ^ 2) + 2 * e1 := by
    exact wavg_add_const hPn.2 _ _
  have F3 : ∑ n, regP T rl (n - c) * (∑ k, regP T rm k * (Y n k) ^ 2) =
      ∑ k, regP T rm k * ∑ n, regP T rl (n - c) * (Y n k) ^ 2 := by
    simp only [mul_sum]; rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have F4 : ∑ k, regP T rm k * ∑ n, regP T rl (n - c) * (Y n k) ^ 2 ≤ √ε + e2 :=
    wavg_le hPk.1 hPk.2 _ fun k hk => hD k hk
  simp only [hX] at F1
  linarith

/-- **Estimate (op)** of Lemma 9.6 (dual form of (po)). -/
theorem wmix_op {T : Finset (ZMod p)} {rl rm r10 r11 ε : ℝ} (hrl : 0 < rl) (hrm : 0 < rm)
    (hr10 : 0 < r10) (hr11 : 0 < r11) (h4m : 4 * r11 ≤ rm) (h4l : 4 * (rm + r10) ≤ rl)
    (f G : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hG : ∀ x, |G x| ≤ 1) (c : ZMod p)
    (hU : ∑ u, regP T rl (u - c) * U2f T r10 r11 f u ≤ ε) :
    ∑ k, regP T rm k * |∑ n, regP T rl (n - c) * (f (n - k) * G n)| ≤
      √(√ε + 50 * T.card * (rm + r10) / rl + 2 * (50 * T.card * r11 / rm)) := by
  have hPn := regP_center_isDist T hrl.le c
  have hPk := regP_isDist T hrm.le
  set Z : ZMod p → ℝ := fun k => ∑ n, regP T rl (n - c) * (f (n - k) * G n) with hZ
  set s : ZMod p → ℝ := fun k => if 0 ≤ Z k then 1 else -1 with hs
  have hsb : ∀ k, |s k| ≤ 1 := fun k => by simp only [hs]; split_ifs <;> simp
  have habs : ∀ k, |Z k| = s k * Z k := fun k => by
    simp only [hs]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · push_neg at h; rw [abs_of_neg h]; ring
  have hpo := wmix_po hrl hrm hr10 hr11 h4m h4l f s hf hsb c hU
  simp only [hZ] at habs
  have e : ∑ k, regP T rm k * |∑ n, regP T rl (n - c) * (f (n - k) * G n)| =
      ∑ n, regP T rl (n - c) * (G n * ∑ k, regP T rm k * (f (n - k) * s k)) := by
    simp only [habs, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [e]
  have h1 : ∑ n, regP T rl (n - c) * (G n * ∑ k, regP T rm k * (f (n - k) * s k)) ≤
      ∑ n, regP T rl (n - c) * |∑ k, regP T rm k * (f (n - k) * s k)| := by
    refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (hPn.1 n)
    calc G n * ∑ k, regP T rm k * (f (n - k) * s k)
        ≤ |G n * ∑ k, regP T rm k * (f (n - k) * s k)| := le_abs_self _
      _ = |G n| * |∑ k, regP T rm k * (f (n - k) * s k)| := abs_mul _ _
      _ ≤ 1 * |∑ k, regP T rm k * (f (n - k) * s k)| := by gcongr; exact hG n
      _ = _ := one_mul _
  have h2 : (∑ n, regP T rl (n - c) * |∑ k, regP T rm k * (f (n - k) * s k)|) ^ 2 ≤
      ∑ n, regP T rl (n - c) * (∑ k, regP T rm k * (f (n - k) * s k)) ^ 2 := by
    have := sq_wavg_le (fun n => |∑ k, regP T rm k * (f (n - k) * s k)|) hPn.1 hPn.2
    simpa only [sq_abs] using this
  have h0 : 0 ≤ ∑ n, regP T rl (n - c) * |∑ k, regP T rm k * (f (n - k) * s k)| :=
    sum_nonneg fun n _ => mul_nonneg (hPn.1 n) (abs_nonneg _)
  refine h1.trans ?_
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt (h2.trans hpo)

section conc

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

omit hPR in
lemma wmix_err_le (i : Fin 4) {m : ℕ} (hm : lvl i < m) (hm10 : m ≤ 10) :
    50 * T.card * (R (j + m) + R (j + 10)) / R (j + lvl i) +
      2 * (50 * T.card * R (j + 11) / R (j + m)) ≤ 200 * T.card * θ := by
  have hθ1' : θ ≤ 1 := by linarith
  have h1 := ratio_sum2 hR0 hRk hθ0 hθ1 (show j + lvl i < j + m by omega)
    (show j + lvl i < j + 10 by have := lvl_le i; omega)
  have h2 := ratio_le_sc hR0 hRk hθ0 hθ1' (50 * T.card) (by positivity)
    (show j + m < j + 11 by omega)
  have hT : (0 : ℝ) ≤ 50 * T.card := by positivity
  have e : 50 * T.card * (R (j + m) + R (j + 10)) / R (j + lvl i) =
      50 * T.card * ((R (j + m) + R (j + 10)) / R (j + lvl i)) := by ring
  rw [e]
  nlinarith

/-- (po) for the balanced functions of a pseudorandom neighbourhood. -/
theorem conc_po (i : Fin 4) {m : ℕ} (hm : lvl i < m) (hm10 : m ≤ 10) (G : ZMod p → ℝ)
    (hG : ∀ x, |G x| ≤ 1) :
    ∑ n, regP T (R (j + lvl i)) (n - cent c i) *
      (∑ k, regP T (R (j + m)) k * (bal R A T c j i (n - k) * G k)) ^ 2 ≤
      √ε4 + 200 * T.card * θ := by
  have hθ1' : θ ≤ 1 := by linarith
  have := wmix_po (hR0 _) (hR0 _) (hR0 _) (hR0 _)
    (four_R_le hR0 hRk hθ0 hθ1' (show j + m < j + 11 by omega) hθ1)
    (four_R2_le hR0 hRk hθ0 hθ1' (show j + lvl i < j + m by omega)
      (show j + lvl i < j + 10 by have := lvl_le i; omega) hθ1)
    (bal R A T c j i) G (abs_bal_le A T c j i (hR0 _).le) hG (cent c i) (hPR i)
  have := wmix_err_le hR0 hRk hθ0 hθ1 (T := T) (j := j) i hm hm10
  linarith

/-- (op) for the balanced functions of a pseudorandom neighbourhood. -/
theorem conc_op (i : Fin 4) {m : ℕ} (hm : lvl i < m) (hm10 : m ≤ 10) (G : ZMod p → ℝ)
    (hG : ∀ x, |G x| ≤ 1) :
    ∑ k, regP T (R (j + m)) k *
      |∑ n, regP T (R (j + lvl i)) (n - cent c i) * (bal R A T c j i (n - k) * G n)| ≤
      √(√ε4 + 200 * T.card * θ) := by
  have hθ1' : θ ≤ 1 := by linarith
  have := wmix_op (hR0 _) (hR0 _) (hR0 _) (hR0 _)
    (four_R_le hR0 hRk hθ0 hθ1' (show j + m < j + 11 by omega) hθ1)
    (four_R2_le hR0 hRk hθ0 hθ1' (show j + lvl i < j + m by omega)
      (show j + lvl i < j + 10 by have := lvl_le i; omega) hθ1)
    (bal R A T c j i) G (abs_bal_le A T c j i (hR0 _).le) hG (cent c i) (hPR i)
  refine this.trans (Real.sqrt_le_sqrt ?_)
  have := wmix_err_le hR0 hRk hθ0 hθ1 (T := T) (j := j) i hm hm10
  linarith

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

/-- `E|X| ≤ (E X²)^{1/2}`. -/
lemma wavg_abs_le_sqrt (X : α → ℝ) : ∑ x, P x * |X x| ≤ √(∑ x, P x * (X x) ^ 2) := by
  have h0 : 0 ≤ ∑ x, P x * |X x| := sum_nonneg fun x _ => mul_nonneg (hP x) (abs_nonneg _)
  rw [← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  have := sq_wavg_le (fun x => |X x|) hP hP1
  simpa only [sq_abs] using this

end prob

/-! ### The data of the fifth step -/

lemma I12_nonneg (A : Fin 4 → Finset (ZMod p)) (a a2 : ZMod p) : 0 ≤ I12 A a a2 :=
  mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _)

lemma I12_le_one (A : Fin 4 → Finset (ZMod p)) (a a2 : ZMod p) : I12 A a a2 ≤ 1 :=
  mul_le_one₀ (ind_le_one _ _) (ind_nonneg _ _) (ind_le_one _ _)

open Classical in
lemma vb_nonneg (S : Finset (ZMod p)) (ρv : ℝ) (l : ZMod p) : 0 ≤ vb S ρv l := by
  unfold vb; split_ifs <;> norm_num

open Classical in
lemma vb_le_one (S : Finset (ZMod p)) (ρv : ℝ) (l : ZMod p) : vb S ρv l ≤ 1 := by
  unfold vb; split_ifs <;> norm_num

end

end GT
end File_GT_U3S5b

section File_GT_U3S5c
/-!
# Local inverse `U³`, fifth step: concentration of `g₁₂`, `g₃₄` and the weighted average
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma alph_eq_sum (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) :
    alph R A T c j i = ∑ x, regP T (R (j + lvl i)) x * ind (A i) (cent c i + x) := by
  unfold alph; rw [sum_regP_center_shift]

/-- Reindexing a sum over `a` weighted around `aC c` by `n = a - b`. -/
lemma sum_reindex_sub (T : Finset (ZMod p)) (ρ : ℝ) (a0 b : ZMod p) (F : ZMod p → ℝ) :
    ∑ a, regP T ρ (a - a0) * F (a - b) = ∑ n, regP T ρ (n - (a0 - b)) * F n := by
  refine Fintype.sum_equiv (Equiv.subRight b) _ _ (fun a => ?_)
  simp only [Equiv.subRight_apply]
  congr 2; ring

section conc

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

/-- Concentration of `g₁₂` (estimate (po-2)). -/
theorem g12_conc :
    ∑ a, regP T (R j) (a - aC c) *
      (g12 R A T c j a - alph R A T c j 0 * alph R A T c j 1) ^ 2 ≤
      √ε4 + 200 * T.card * θ := by
  have h := conc_po hR0 hRk hθ0 hθ1 hPR 0 (m := 2) (by decide) (by norm_num)
    (fun k => ind (A 1) (cent c 1 + k)) (fun k => by
      rw [abs_of_nonneg (ind_nonneg _ _)]; exact ind_le_one _ _)
  have e : ∀ a, g12 R A T c j a - alph R A T c j 0 * alph R A T c j 1 =
      ∑ k, regP T (R (j + 2)) k * (bal R A T c j 0 (a - cent c 1 - k) *
        ind (A 1) (cent c 1 + k)) := by
    intro a
    rw [alph_eq_sum R A T c j 1]
    simp only [g12, I12, bal, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [show a - (cent c 1 + k) = a - cent c 1 - k by ring]
    have : lvl 1 = 2 := rfl
    rw [this]; ring
  simp_rw [e]
  have e2 := sum_reindex_sub T (R j) (aC c) (cent c 1) (fun n => (∑ k, regP T (R (j + 2)) k *
    (bal R A T c j 0 (n - k) * ind (A 1) (cent c 1 + k))) ^ 2)
  (try simp only at e2)
  rw [e2, show aC c - cent c 1 = cent c 0 by simp [aC]]
  exact h

end conc

end

end GT
end File_GT_U3S5c

section File_GT_U3S6a
/-!
# Local inverse `U³`, Proposition 9.8 (`ξ'` respects almost all additive quadruples):
concentration estimates
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma abs_ind_le (A : Finset (ZMod p)) (u : ZMod p) : |ind A u| ≤ 1 := by
  rw [abs_of_nonneg (ind_nonneg _ _)]; exact ind_le_one _ _

section conc6

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

/-- Estimate (op) for `A₂`: `E_h |E_{a₂} 1_{A₂}(a₂) 1_{A₂}(a₂ + h) - α₂²| ≤ √δ`. -/
theorem conc_F :
    ∑ h, regP T (R (j + 3)) h * |∑ x, regP T (R (j + 2)) x *
      (ind (A 1) (cent c 1 + x) * ind (A 1) (cent c 1 + x + h)) -
        alph R A T c j 1 * alph R A T c j 1| ≤ √(√ε4 + 200 * T.card * θ) := by
  have H := conc_op hR0 hRk hθ0 hθ1 hPR 1 (m := 3) (by decide) (by norm_num)
    (fun n => ind (A 1) n) (fun n => abs_ind_le _ _)
  have hl : lvl 1 = 2 := rfl
  rw [hl] at H
  rw [← sum_regP_neg_real]
  refine le_of_eq_of_le (sum_congr rfl fun k _ => ?_) H
  congr 2
  rw [sum_regP_center_shift, alph_eq_sum R A T c j 1, hl, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  simp only [bal, hl, alph_eq_sum R A T c j 1]
  rw [show cent c 1 + x - k = cent c 1 + x + -k by ring]
  ring

/-- Estimate (po) for `A₂`: `E_{a₂} |E_h 1_{A₂}(a₂ + h) - α₂| ≤ √δ`. -/
theorem conc_G1 :
    ∑ x, regP T (R (j + 2)) x * |∑ h, regP T (R (j + 3)) h * ind (A 1) (cent c 1 + x + h) -
      alph R A T c j 1| ≤ √(√ε4 + 200 * T.card * θ) := by
  have H := conc_po hR0 hRk hθ0 hθ1 hPR 1 (m := 3) (by decide) (by norm_num)
    (fun _ => 1) (fun _ => by norm_num)
  have hl : lvl 1 = 2 := rfl
  rw [hl, sum_regP_center_shift] at H
  have hP := regP_isDist T (hR0 (j + 2)).le
  refine (wavg_abs_le_sqrt hP.1 hP.2 _).trans (Real.sqrt_le_sqrt (le_of_eq_of_le
    (sum_congr rfl fun x _ => ?_) H))
  congr 1
  have hQ := regP_isDist T (hR0 (j + 3)).le
  rw [← sum_regP_neg_real]
  simp only [bal, mul_one, mul_sub, sum_sub_distrib, ← sum_mul, hQ.2, one_mul]
  congr 2
  refine sum_congr rfl fun h _ => ?_
  rw [show cent c 1 + x + -h = cent c 1 + x - h by ring]

/-- Estimate (po) for `A₁`, in the form used repeatedly: for `|G| ≤ 1`,
`E_a |E_{a₂} 1_{A₁}(a - a₂) G(a₂) - α₁ E_{a₂} G(a₂)| ≤ √δ`. -/
theorem conc_A0 (G : ZMod p → ℝ) (hG : ∀ x, |G x| ≤ 1) :
    ∑ a, regP T (R j) (a - aC c) * |∑ x, regP T (R (j + 2)) x *
      (ind (A 0) (a - (cent c 1 + x)) * G x) -
        alph R A T c j 0 * ∑ x, regP T (R (j + 2)) x * G x| ≤ √(√ε4 + 200 * T.card * θ) := by
  have H := conc_po hR0 hRk hθ0 hθ1 hPR 0 (m := 2) (by decide) (by norm_num) G hG
  have hl : lvl 0 = 0 := rfl
  rw [hl, add_zero] at H
  have hP := regP_center_isDist T (hR0 j).le (aC c)
  refine (wavg_abs_le_sqrt hP.1 hP.2 _).trans (Real.sqrt_le_sqrt ?_)
  have e : ∀ a, (∑ x, regP T (R (j + 2)) x * (ind (A 0) (a - (cent c 1 + x)) * G x) -
      alph R A T c j 0 * ∑ x, regP T (R (j + 2)) x * G x) =
      ∑ k, regP T (R (j + 2)) k * (bal R A T c j 0 (a - cent c 1 - k) * G k) := by
    intro a
    simp only [bal, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [show a - (cent c 1 + k) = a - cent c 1 - k by ring]
    ring
  simp_rw [e]
  have e2 := sum_reindex_sub T (R j) (aC c) (cent c 1) (fun n => (∑ k, regP T (R (j + 2)) k *
    (bal R A T c j 0 (n - k) * G k)) ^ 2)
  (try simp only at e2)
  rw [e2, show aC c - cent c 1 = cent c 0 by simp [aC]]
  exact H

end conc6

end

end GT
end File_GT_U3S6a

section File_GT_U3S6b
/-!
# Local inverse `U³`, Proposition 9.8: averaging tools
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma abs_wavg_le1 {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (F : α → ℝ) (hF : ∀ x, |F x| ≤ 1) : |∑ x, P x * F x| ≤ 1 :=
  abs_wavg_le hP hP1 F fun x _ => hF x

lemma abs_wavg_sub_le {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (F G : α → ℝ) {B : ℝ} (h : ∀ x, |F x - G x| ≤ B) :
    |∑ x, P x * F x - ∑ x, P x * G x| ≤ B := by
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  exact abs_wavg_le hP hP1 _ fun x _ => h x

/-- Simultaneous translation of three independent regular variables. -/
lemma shift3 {T : Finset (ZMod p)} {ρa ρx σ : ℝ} (hρa : 0 < ρa) (hρx : 0 < ρx)
    (h4a : 4 * σ ≤ ρa) (h4x : 4 * σ ≤ ρx) {s : ZMod p} (hs : snorm T s ≤ σ) (n0 : ZMod p)
    (Φ : ZMod p → ZMod p → ZMod p → ℝ) (hΦ : ∀ u v y, |Φ u v y| ≤ 1) :
    |∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x *
        Φ (a + s) (b + s) (x + s) -
      ∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x * Φ a b x| ≤
      2 * (50 * T.card * σ / ρa) + 50 * T.card * σ / ρx := by
  have hPa := regP_center_isDist T hρa.le n0
  have hQ := regP_isDist T hρx.le
  have hin : ∀ u v, |∑ x, regP T ρx x * Φ u v (x + s)| ≤ 1 := fun u v =>
    abs_wavg_le1 hQ.1 hQ.2 _ fun x => hΦ _ _ _
  have hin2 : ∀ u, |∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x * Φ u (b + s) (x + s)| ≤ 1 :=
    fun u => abs_wavg_le1 hPa.1 hPa.2 _ fun b => hin _ _
  -- shift `a`
  have s1 := shift_real_c subset_rfl hρa h4a hs n0
    (fun u => ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x * Φ u (b + s) (x + s)) hin2
  -- shift `b`
  have s2 : |∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x *
        Φ a (b + s) (x + s) -
      ∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x * Φ a b (x + s)| ≤
      50 * T.card * σ / ρa := by
    refine abs_wavg_sub_le hPa.1 hPa.2 _ _ fun a => ?_
    have := shift_real_c subset_rfl hρa h4a hs n0
      (fun v => ∑ x, regP T ρx x * Φ a v (x + s)) (fun v => hin _ _)
    simpa using this
  -- shift `x`
  have s3 : |∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x *
        Φ a b (x + s) -
      ∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x * Φ a b x| ≤
      50 * T.card * σ / ρx := by
    refine abs_wavg_sub_le hPa.1 hPa.2 _ _ fun a => ?_
    refine abs_wavg_sub_le hPa.1 hPa.2 _ _ fun b => ?_
    have := shift_real subset_rfl hρx h4x hs (fun y => Φ a b y) (fun y => hΦ _ _ _)
    simpa using this
  simp only [one_mul] at s1
  have := abs_sub_le (∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x *
        Φ (a + s) (b + s) (x + s))
    (∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x *
        Φ a (b + s) (x + s))
    (∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x * Φ a b (x + s))
  have := abs_sub_le (∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x *
        Φ (a + s) (b + s) (x + s))
    (∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x * Φ a b (x + s))
    (∑ a, regP T ρa (a - n0) * ∑ b, regP T ρa (b - n0) * ∑ x, regP T ρx x * Φ a b x)
  linarith

lemma wswap {α β : Type*} [Fintype α] [Fintype β] (P : α → ℝ) (Q : β → ℝ) (F : α → β → ℝ) :
    ∑ a, P a * ∑ x, Q x * F a x = ∑ x, Q x * ∑ a, P a * F a x := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma wsum_le_add_abs {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (Z : α → ℝ) (K : ℝ) :
    ∑ x, P x * Z x ≤ K + ∑ x, P x * |Z x - K| := by
  have : ∑ x, P x * Z x - K = ∑ x, P x * (Z x - K) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP1, one_mul]
  have h2 : ∑ x, P x * (Z x - K) ≤ ∑ x, P x * |Z x - K| :=
    sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (le_abs_self _) (hP x)
  linarith

/-- `E_h 1_{A₂}(a₂ + h)`. -/
def G1f (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) (x : ZMod p) : ℝ :=
  ∑ h, regP T (R (j + 3)) h * ind (A 1) (cent c 1 + x + h)

/-- `E_{a'} 1_{A₁}(a' - a₂)`. -/
def H0f (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) (x : ZMod p) : ℝ :=
  ∑ b, regP T (R j) (b - aC c) * ind (A 0) (b - (cent c 1 + x))

/-- The quadruple count `E_{a₂} 1_{A₂}(a₂) 1_{A₂}(a₂+h) 1_{A₁}(a-a₂) 1_{A₁}(b-a₂)`. -/
def EIf (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) (h a b : ZMod p) : ℝ :=
  ∑ x, regP T (R (j + 2)) x * (ind (A 0) (b - (cent c 1 + x)) *
    (ind (A 0) (a - (cent c 1 + x)) * (ind (A 1) (cent c 1 + x) * ind (A 1) (cent c 1 + x + h))))

section pen

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

/-- The basic estimate for the penalty terms of Proposition 9.8. -/
theorem pf_bound (Y : ZMod p → ZMod p → ℝ) (hY0 : ∀ a x, 0 ≤ Y a x) (hY1 : ∀ a x, Y a x ≤ 1) :
    ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
      (Y a x * (G1f R A T c j x * H0f R A T c j x)) ≤
      alph R A T c j 1 * (alph R A T c j 0 * ∑ a, regP T (R j) (a - aC c) *
        ∑ x, regP T (R (j + 2)) x * Y a x + √(√ε4 + 200 * T.card * θ)) +
      √(√ε4 + 200 * T.card * θ) := by
  set δ := √(√ε4 + 200 * T.card * θ)
  set α0 := alph R A T c j 0
  set α1 := alph R A T c j 1
  have hPa := regP_center_isDist T (hR0 j).le (aC c)
  have hP2 := regP_isDist T (hR0 (j + 2)).le
  have hP3 := regP_isDist T (hR0 (j + 3)).le
  have hG : ∀ x, 0 ≤ G1f R A T c j x ∧ G1f R A T c j x ≤ 1 := fun x =>
    ⟨sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _) (ind_nonneg _ _),
      wavg_le hP3.1 hP3.2 _ fun _ _ => ind_le_one _ _⟩
  have hH : ∀ x, 0 ≤ H0f R A T c j x ∧ H0f R A T c j x ≤ 1 := fun x =>
    ⟨sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _) (ind_nonneg _ _),
      wavg_le hPa.1 hPa.2 _ fun _ _ => ind_le_one _ _⟩
  have hα1 : 0 ≤ α1 := alph_nonneg R A T c j 1
  have hα0 : 0 ≤ α0 := alph_nonneg R A T c j 0
  -- pointwise
  have hpt : ∀ a x, Y a x * (G1f R A T c j x * H0f R A T c j x) ≤
      α1 * (Y a x * H0f R A T c j x) + |G1f R A T c j x - α1| := by
    intro a x
    have hYH0 : 0 ≤ Y a x * H0f R A T c j x := mul_nonneg (hY0 a x) (hH x).1
    have hYH1 : Y a x * H0f R A T c j x ≤ 1 :=
      mul_le_one₀ (hY1 a x) (hH x).1 (hH x).2
    have e : Y a x * (G1f R A T c j x * H0f R A T c j x) =
        α1 * (Y a x * H0f R A T c j x) + (Y a x * H0f R A T c j x) * (G1f R A T c j x - α1) := by
      ring
    have i1 := mul_le_mul_of_nonneg_left (le_abs_self (G1f R A T c j x - α1)) hYH0
    have i2 := mul_le_of_le_one_left (abs_nonneg (G1f R A T c j x - α1)) hYH1
    linarith
  have step1 : ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
      (Y a x * (G1f R A T c j x * H0f R A T c j x)) ≤
      α1 * ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
        (Y a x * H0f R A T c j x) +
      ∑ x, regP T (R (j + 2)) x * |G1f R A T c j x - α1| := by
    have e : ∀ a, ∑ x, regP T (R (j + 2)) x * (α1 * (Y a x * H0f R A T c j x) +
        |G1f R A T c j x - α1|) = α1 * ∑ x, regP T (R (j + 2)) x * (Y a x * H0f R A T c j x) +
        ∑ x, regP T (R (j + 2)) x * |G1f R A T c j x - α1| := by
      intro a
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1; exact sum_congr rfl fun _ _ => by ring
    calc _ ≤ ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
          (α1 * (Y a x * H0f R A T c j x) + |G1f R A T c j x - α1|) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (hpt a x) (regP_nonneg _ _)) (regP_nonneg _ _)
      _ = _ := by
          simp_rw [e]
          rw [wavg_add_const hPa.2, mul_sum]
          congr 1; exact sum_congr rfl fun _ _ => by ring
  have hG1c : ∑ x, regP T (R (j + 2)) x * |G1f R A T c j x - α1| ≤ δ :=
    conc_G1 hR0 hRk hθ0 hθ1 hPR
  -- the `H` average
  set y : ZMod p → ℝ := fun x => ∑ a, regP T (R j) (a - aC c) * Y a x with hy
  have hy1 : ∀ x, |y x| ≤ 1 := fun x => abs_wavg_le1 hPa.1 hPa.2 _ fun a => by
    rw [abs_of_nonneg (hY0 a x)]; exact hY1 a x
  have step2 : ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
      (Y a x * H0f R A T c j x) = ∑ b, regP T (R j) (b - aC c) *
        ∑ x, regP T (R (j + 2)) x * (ind (A 0) (b - (cent c 1 + x)) * y x) := by
    rw [wswap (fun a => regP T (R j) (a - aC c)) (fun x => regP T (R (j + 2)) x)
      (fun a x => Y a x * H0f R A T c j x)]
    rw [wswap (fun b => regP T (R j) (b - aC c)) (fun x => regP T (R (j + 2)) x)
      (fun b x => ind (A 0) (b - (cent c 1 + x)) * y x)]
    refine sum_congr rfl fun x _ => ?_
    congr 1
    simp only [H0f, hy, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hA0 := conc_A0 hR0 hRk hθ0 hθ1 hPR y hy1
  have step3 := wsum_le_add_abs hPa.1 hPa.2
    (fun b => ∑ x, regP T (R (j + 2)) x * (ind (A 0) (b - (cent c 1 + x)) * y x))
    (α0 * ∑ x, regP T (R (j + 2)) x * y x)
  have e4 : ∑ x, regP T (R (j + 2)) x * y x =
      ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x * Y a x := by
    rw [wswap (fun a => regP T (R j) (a - aC c)) (fun x => regP T (R (j + 2)) x)]
  rw [e4] at step3 hA0
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  rw [step2] at step1
  have h5 : ∑ b, regP T (R j) (b - aC c) *
      ∑ x, regP T (R (j + 2)) x * (ind (A 0) (b - (cent c 1 + x)) * y x) ≤
      α0 * ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x * Y a x + δ := by
    linarith
  have := mul_le_mul_of_nonneg_left h5 hα1
  linarith

/-- Concentration of the quadruple count (estimate (pen1) of Proposition 9.8). -/
theorem ei_bound :
    ∑ h, regP T (R (j + 3)) h * ∑ a, regP T (R j) (a - aC c) * ∑ b, regP T (R j) (b - aC c) *
      |EIf R A T c j h a b - (alph R A T c j 0 * alph R A T c j 1) ^ 2| ≤
      3 * √(√ε4 + 200 * T.card * θ) := by
  set δ := √(√ε4 + 200 * T.card * θ)
  set α0 := alph R A T c j 0
  set α1 := alph R A T c j 1
  have hPa := regP_center_isDist T (hR0 j).le (aC c)
  have hP3 := regP_isDist T (hR0 (j + 3)).le
  have hα0 : 0 ≤ α0 := alph_nonneg R A T c j 0
  have hα0' : α0 ≤ 1 := alph_le_one A T c j 0 (hR0 _).le
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  set F : ZMod p → ℝ := fun h => ∑ x, regP T (R (j + 2)) x *
    (ind (A 1) (cent c 1 + x) * ind (A 1) (cent c 1 + x + h)) with hF
  set F' : ZMod p → ZMod p → ℝ := fun h a => ∑ x, regP T (R (j + 2)) x *
    (ind (A 0) (a - (cent c 1 + x)) * (ind (A 1) (cent c 1 + x) * ind (A 1) (cent c 1 + x + h)))
    with hF'
  have T1 : ∀ h a, ∑ b, regP T (R j) (b - aC c) * |EIf R A T c j h a b - α0 * F' h a| ≤ δ :=
    fun h a => conc_A0 hR0 hRk hθ0 hθ1 hPR
      (fun x => ind (A 0) (a - (cent c 1 + x)) * (ind (A 1) (cent c 1 + x) *
        ind (A 1) (cent c 1 + x + h)))
      (fun x => by
        rw [abs_mul, abs_mul]
        exact mul_le_one₀ (abs_ind_le _ _) (by positivity)
          (mul_le_one₀ (abs_ind_le _ _) (abs_nonneg _) (abs_ind_le _ _)))
  have T2 : ∀ h, ∑ a, regP T (R j) (a - aC c) * |F' h a - α0 * F h| ≤ δ :=
    fun h => conc_A0 hR0 hRk hθ0 hθ1 hPR
      (fun x => ind (A 1) (cent c 1 + x) * ind (A 1) (cent c 1 + x + h))
      (fun x => by
        rw [abs_mul]
        exact mul_le_one₀ (abs_ind_le _ _) (abs_nonneg _) (abs_ind_le _ _))
  have T3 : ∑ h, regP T (R (j + 3)) h * |F h - α1 * α1| ≤ δ := conc_F hR0 hRk hθ0 hθ1 hPR
  have hpt : ∀ h a b, |EIf R A T c j h a b - (α0 * α1) ^ 2| ≤
      |EIf R A T c j h a b - α0 * F' h a| + (α0 * |F' h a - α0 * F h| +
        α0 ^ 2 * |F h - α1 * α1|) := by
    intro h a b
    have e : EIf R A T c j h a b - (α0 * α1) ^ 2 = (EIf R A T c j h a b - α0 * F' h a) +
        (α0 * (F' h a - α0 * F h) + α0 ^ 2 * (F h - α1 * α1)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ((abs_add_le _ _).trans ?_))
    rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_of_nonneg (sq_nonneg α0)]
  have inner : ∀ h a, ∑ b, regP T (R j) (b - aC c) * |EIf R A T c j h a b - (α0 * α1) ^ 2| ≤
      δ + (α0 * |F' h a - α0 * F h| + α0 ^ 2 * |F h - α1 * α1|) := by
    intro h a
    calc _ ≤ ∑ b, regP T (R j) (b - aC c) * (|EIf R A T c j h a b - α0 * F' h a| +
          (α0 * |F' h a - α0 * F h| + α0 ^ 2 * |F h - α1 * α1|)) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hpt h a b) (regP_nonneg _ _)
      _ = ∑ b, regP T (R j) (b - aC c) * |EIf R A T c j h a b - α0 * F' h a| +
          (α0 * |F' h a - α0 * F h| + α0 ^ 2 * |F h - α1 * α1|) := wavg_add_const hPa.2 _ _
      _ ≤ _ := by linarith [T1 h a]
  have inner2 : ∀ h, ∑ a, regP T (R j) (a - aC c) *
      (δ + (α0 * |F' h a - α0 * F h| + α0 ^ 2 * |F h - α1 * α1|)) ≤
      α0 * δ + (δ + α0 ^ 2 * |F h - α1 * α1|) := by
    intro h
    have e : ∀ a, δ + (α0 * |F' h a - α0 * F h| + α0 ^ 2 * |F h - α1 * α1|) =
        α0 * |F' h a - α0 * F h| + (δ + α0 ^ 2 * |F h - α1 * α1|) := fun a => by ring
    simp_rw [e]
    rw [wavg_add_const hPa.2]
    have e2 : ∑ a, regP T (R j) (a - aC c) * (α0 * |F' h a - α0 * F h|) =
        α0 * ∑ a, regP T (R j) (a - aC c) * |F' h a - α0 * F h| := by
      rw [Finset.mul_sum univ (fun a => regP T (R j) (a - aC c) * |F' h a - α0 * F h|) α0]
      exact sum_congr rfl fun _ _ => by ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left (T2 h) hα0
    linarith
  calc _ ≤ ∑ h, regP T (R (j + 3)) h * (α0 * δ + (δ + α0 ^ 2 * |F h - α1 * α1|)) := by
        refine sum_le_sum fun h _ => mul_le_mul_of_nonneg_left ?_ (regP_nonneg _ _)
        exact (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (inner h a)
          (regP_nonneg _ _)).trans (inner2 h)
    _ = α0 * δ + δ + α0 ^ 2 * ∑ h, regP T (R (j + 3)) h * |F h - α1 * α1| := by
        have e3 : ∀ h, α0 * δ + (δ + α0 ^ 2 * |F h - α1 * α1|) =
            α0 ^ 2 * |F h - α1 * α1| + (α0 * δ + δ) := fun h => by ring
        simp_rw [e3]
        rw [wavg_add_const hP3.2, mul_sum]
        have : ∑ i, regP T (R (j + 3)) i * (α0 ^ 2 * |F i - α1 * α1|) =
            ∑ i, α0 ^ 2 * (regP T (R (j + 3)) i * |F i - α1 * α1|) :=
          sum_congr rfl fun _ _ => by ring
        rw [this]; ring
    _ ≤ 3 * δ := by
        have h1 := mul_le_mul_of_nonneg_left T3 (sq_nonneg α0)
        have h2 : α0 ^ 2 ≤ 1 := by nlinarith
        have h3 : α0 * δ ≤ δ := by nlinarith
        have h4 : α0 ^ 2 * δ ≤ δ := by nlinarith
        linarith

end pen

end

end GT
end File_GT_U3S6b

section File_GT_U3S6c
/-!
# Local inverse `U³`, Proposition 9.8: the penalty terms
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The very bad decompositions of `a` through `a₂ = c₁ + x` for the frequency `ξ'`. -/
def Y1 (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p) (A : Fin 4 → Finset (ZMod p))
    (c : Fin 4 → ZMod p) (a x : ZMod p) : ℝ :=
  I12 A a (cent c 1 + x) * vb S ρv (ξ' a - ξ (a - (cent c 1 + x)) - ξ (cent c 1 + x))

lemma Y1_nonneg (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p)
    (A : Fin 4 → Finset (ZMod p)) (c : Fin 4 → ZMod p) (a x : ZMod p) :
    0 ≤ Y1 S ρv ξ ξ' A c a x :=
  mul_nonneg (I12_nonneg _ _ _) (vb_nonneg _ _ _)

lemma Y1_le_one (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p)
    (A : Fin 4 → Finset (ZMod p)) (c : Fin 4 → ZMod p) (a x : ZMod p) :
    Y1 S ρv ξ ξ' A c a x ≤ 1 :=
  mul_le_one₀ (I12_le_one _ _ _) (vb_nonneg _ _ _) (vb_le_one _ _ _)

lemma reorder4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    ∑ h, ∑ a, ∑ b, ∑ x, F h a b x = ∑ a, ∑ x, ∑ h, ∑ b, F h a b x := by
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  calc ∑ h, ∑ b, ∑ x, F h a b x = ∑ h, ∑ x, ∑ b, F h a b x :=
        sum_congr rfl fun h _ => sum_comm
    _ = _ := sum_comm

/-- The first penalty term in factored form. -/
lemma pen1_eq (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (Y : ZMod p → ZMod p → ℝ) :
    ∑ h, regP T (R (j + 3)) h * ∑ a, regP T (R j) (a - aC c) * ∑ b, regP T (R j) (b - aC c) *
      ∑ x, regP T (R (j + 2)) x * (ind (A 0) (b - (cent c 1 + x)) *
        ind (A 1) (cent c 1 + x + h) * Y a x) =
      ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
        (Y a x * (G1f R A T c j x * H0f R A T c j x)) := by
  simp only [G1f, H0f, sum_mul, mul_sum]
  rw [reorder4]
  refine sum_congr rfl fun a _ => sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun h _ => ?_
  ring

/-- The third penalty term (shifted decompositions) reduces to the factored form. -/
lemma pen3_le {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (Y : ZMod p → ZMod p → ℝ) (hY0 : ∀ a x, 0 ≤ Y a x)
    (hY1 : ∀ a x, Y a x ≤ 1) :
    ∑ h, regP T (R (j + 3)) h * ∑ a, regP T (R j) (a - aC c) * ∑ b, regP T (R j) (b - aC c) *
      ∑ x, regP T (R (j + 2)) x * (ind (A 0) (b - (cent c 1 + x)) *
        ind (A 1) (cent c 1 + x) * Y (a + h) (x + h)) ≤
      ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
        (Y a x * (G1f R A T c j x * H0f R A T c j x)) +
      (2 * (50 * T.card * R (j + 3) / R j) + 50 * T.card * R (j + 3) / R (j + 2)) := by
  set err := 2 * (50 * T.card * R (j + 3) / R j) + 50 * T.card * R (j + 3) / R (j + 2)
  have hθ1' : θ ≤ 1 := by linarith
  have hP3 := regP_isDist T (hR0 (j + 3)).le
  have h4a : 4 * R (j + 3) ≤ R j := four_R_le hR0 hRk hθ0 hθ1' (show j < j + 3 by omega) hθ1
  have h4x : 4 * R (j + 3) ≤ R (j + 2) :=
    four_R_le hR0 hRk hθ0 hθ1' (show j + 2 < j + 3 by omega) hθ1
  set J : ZMod p → ℝ := fun h => ∑ a, regP T (R j) (a - aC c) * ∑ b, regP T (R j) (b - aC c) *
      ∑ x, regP T (R (j + 2)) x * (ind (A 0) (b - (cent c 1 + x)) *
        ind (A 1) (cent c 1 + x + -h) * Y a x) with hJ
  have key : ∀ h, regP T (R (j + 3)) h ≠ 0 →
      ∑ a, regP T (R j) (a - aC c) * ∑ b, regP T (R j) (b - aC c) *
        ∑ x, regP T (R (j + 2)) x * (ind (A 0) (b - (cent c 1 + x)) *
          ind (A 1) (cent c 1 + x) * Y (a + h) (x + h)) ≤ J h + err := by
    intro h hh
    have hs : snorm T h ≤ R (j + 3) :=
      snorm_le_of_mem (mem_bohr_of_regP_ne_zero (hR0 _).le hh) (hR0 _).le
    have S3 := shift3 (hR0 j) (hR0 (j + 2)) h4a h4x hs (aC c)
      (fun u v y => ind (A 0) (v - (cent c 1 + y)) * ind (A 1) (cent c 1 + y + -h) * Y u y)
      (fun u v y => by
        rw [abs_mul, abs_mul, abs_of_nonneg (hY0 u y)]
        exact mul_le_one₀ (mul_le_one₀ (abs_ind_le _ _) (abs_nonneg _) (abs_ind_le _ _))
          (hY0 u y) (hY1 u y))
    have e : ∀ a b x, ind (A 0) (b + h - (cent c 1 + (x + h))) *
        ind (A 1) (cent c 1 + (x + h) + -h) * Y (a + h) (x + h) =
        ind (A 0) (b - (cent c 1 + x)) * ind (A 1) (cent c 1 + x) * Y (a + h) (x + h) := by
      intro a b x
      rw [show b + h - (cent c 1 + (x + h)) = b - (cent c 1 + x) by ring,
        show cent c 1 + (x + h) + -h = cent c 1 + x by ring]
    simp only [e] at S3
    have := (abs_le.1 S3).2
    linarith
  calc _ ≤ ∑ h, regP T (R (j + 3)) h * (J h + err) := by
        refine sum_le_sum fun h _ => ?_
        by_cases hh : regP T (R (j + 3)) h = 0
        · rw [hh, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (key h hh) (regP_nonneg _ _)
    _ = ∑ h, regP T (R (j + 3)) h * J h + err := wavg_add_const hP3.2 _ _
    _ = _ := by
        congr 1
        rw [hJ, sum_regP_neg_real T (R (j + 3)) (fun h => ∑ a, regP T (R j) (a - aC c) *
          ∑ b, regP T (R j) (b - aC c) * ∑ x, regP T (R (j + 2)) x *
            (ind (A 0) (b - (cent c 1 + x)) * ind (A 1) (cent c 1 + x + h) * Y a x))]
        exact pen1_eq R A T c j Y

end

end GT
end File_GT_U3S6c

section File_GT_U3S6d
/-!
# Local inverse `U³`, Proposition 9.8 (`ξ'` respects almost all additive quadruples)
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma E3_mono (R : ℕ → ℝ) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    {F G : ZMod p → ZMod p → ZMod p → ℝ} (hFG : ∀ h a b, F h a b ≤ G h a b) :
    E3 R T c j F ≤ E3 R T c j G :=
  sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (sum_le_sum fun _ _ =>
    mul_le_mul_of_nonneg_left (sum_le_sum fun _ _ =>
      mul_le_mul_of_nonneg_left (hFG _ _ _) (regP_nonneg _ _)) (regP_nonneg _ _)) (regP_nonneg _ _)

lemma E3_add (R : ℕ → ℝ) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (F G : ZMod p → ZMod p → ZMod p → ℝ) :
    E3 R T c j (fun h a b => F h a b + G h a b) = E3 R T c j F + E3 R T c j G := by
  simp only [E3, mul_add, sum_add_distrib]

lemma E3_smul (R : ℕ → ℝ) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ) (k : ℝ)
    (F : ZMod p → ZMod p → ZMod p → ℝ) :
    E3 R T c j (fun h a b => k * F h a b) = k * E3 R T c j F := by
  simp only [E3, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma E3_swap (R : ℕ → ℝ) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (F : ZMod p → ZMod p → ZMod p → ℝ) :
    E3 R T c j (fun h a b => F h b a) = E3 R T c j F := by
  unfold E3
  refine sum_congr rfl fun h _ => ?_
  congr 1
  exact wswap _ _ _

/-- Four good decompositions give a good additive quadruple. -/
lemma quad_good {S : Finset (ZMod p)} {B : ℝ} {ξ ξ' : ZMod p → ZMod p} {a b h u v w z : ZMod p}
    (h1 : Good S B (ξ' a - ξ u - ξ v)) (h2 : Good S B (ξ' b - ξ w - ξ v))
    (h3 : Good S B (ξ' (a + h) - ξ u - ξ z)) (h4 : Good S B (ξ' (b + h) - ξ w - ξ z)) :
    Good S (4 * B) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h)) := by
  have := ((h1.sub h3).sub h2).add h4
  have e : ξ' a - ξ u - ξ v - (ξ' (a + h) - ξ u - ξ z) - (ξ' b - ξ w - ξ v) +
      (ξ' (b + h) - ξ w - ξ z) = ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h) := by ring
  rw [e, show B + B + B + B = 4 * B by ring] at this
  exact this

/-- The quadruple indicator. -/
def Iq (A : Fin 4 → Finset (ZMod p)) (c : Fin 4 → ZMod p) (h a b x : ZMod p) : ℝ :=
  ind (A 0) (b - (cent c 1 + x)) *
    (ind (A 0) (a - (cent c 1 + x)) * (ind (A 1) (cent c 1 + x) * ind (A 1) (cent c 1 + x + h)))

/-- The four penalty integrands. -/
def Qs (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p) (A : Fin 4 → Finset (ZMod p))
    (c : Fin 4 → ZMod p) (h a b x : ZMod p) : ℝ :=
  ind (A 0) (b - (cent c 1 + x)) * ind (A 1) (cent c 1 + x + h) * Y1 S ρv ξ ξ' A c a x +
  ind (A 0) (a - (cent c 1 + x)) * ind (A 1) (cent c 1 + x + h) * Y1 S ρv ξ ξ' A c b x +
  (ind (A 0) (b - (cent c 1 + x)) * ind (A 1) (cent c 1 + x) * Y1 S ρv ξ ξ' A c (a + h) (x + h) +
  ind (A 0) (a - (cent c 1 + x)) * ind (A 1) (cent c 1 + x) * Y1 S ρv ξ ξ' A c (b + h) (x + h))

lemma Qs_nonneg (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p)
    (A : Fin 4 → Finset (ZMod p)) (c : Fin 4 → ZMod p) (h a b x : ZMod p) :
    0 ≤ Qs S ρv ξ ξ' A c h a b x := by
  unfold Qs
  have := Y1_nonneg S ρv ξ ξ' A c a x; have := Y1_nonneg S ρv ξ ξ' A c b x
  have := Y1_nonneg S ρv ξ ξ' A c (a + h) (x + h)
  have := Y1_nonneg S ρv ξ ξ' A c (b + h) (x + h)
  have := ind_nonneg (A 0) (b - (cent c 1 + x)); have := ind_nonneg (A 0) (a - (cent c 1 + x))
  have := ind_nonneg (A 1) (cent c 1 + x + h); have := ind_nonneg (A 1) (cent c 1 + x)
  positivity

open Classical in
/-- Pointwise: at a bad quadruple every decomposition is penalised. -/
lemma Iq_le_Qs (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p)
    (A : Fin 4 → Finset (ZMod p)) (c : Fin 4 → ZMod p) (h a b x : ZMod p)
    (hbad : ¬ Good S (4 / ρv) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h))) :
    Iq A c h a b x ≤ Qs S ρv ξ ξ' A c h a b x := by
  have e1 : a + h - (cent c 1 + (x + h)) = a - (cent c 1 + x) := by ring
  have e2 : b + h - (cent c 1 + (x + h)) = b - (cent c 1 + x) := by ring
  have e3 : cent c 1 + (x + h) = cent c 1 + x + h := by ring
  unfold Qs Y1 I12 Iq
  rw [e1, e2, e3]
  have hI0 := ind_nonneg (A 0) (b - (cent c 1 + x))
  have hI1 := ind_nonneg (A 0) (a - (cent c 1 + x))
  have hI2 := ind_nonneg (A 1) (cent c 1 + x)
  have hI3 := ind_nonneg (A 1) (cent c 1 + x + h)
  have hP : 0 ≤ ind (A 0) (b - (cent c 1 + x)) * (ind (A 0) (a - (cent c 1 + x)) *
      (ind (A 1) (cent c 1 + x) * ind (A 1) (cent c 1 + x + h))) := by positivity
  unfold vb
  split_ifs with g1 g2 g3 g4 <;> try nlinarith
  exfalso
  apply hbad
  have := quad_good g1 g2 g3 g4
  rwa [show 4 * (1 / ρv) = 4 / ρv by ring] at this

lemma ind_le_ratio {P : Prop} [Decidable P] {m EI K : ℝ} (hm : 0 < m) (hK0 : 0 ≤ K)
    (hK : ¬P → EI ≤ K) : (if P then (0 : ℝ) else 1) ≤ 2 / m * (|EI - m| + K) := by
  split_ifs with hP
  · have := abs_nonneg (EI - m); positivity
  · have hEK := hK hP
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    have h1 := le_abs_self (EI - m)
    have h2 := neg_abs_le (EI - m)
    by_cases hc : m / 2 ≤ EI
    · linarith
    · push_neg at hc; linarith

section pordo

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Proposition 9.8**: `ξ'` respects almost all additive quadruples in a Bohr neighbourhood. -/
theorem pordo (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p) (Gd : Finset (ZMod p))
    {t e5 : ℝ} (ht : 0 ≤ t) (hpos : 0 < alph R A T c j 0 * alph R A T c j 1)
    (hGd1 : ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) ≤ e5)
    (hGd2 : ∀ a ∈ Gd, ∑ x, regP T (R (j + 2)) x * (I12 A a (cent c 1 + x) *
      vb S ρv (ξ' a - ξ (a - (cent c 1 + x)) - ξ (cent c 1 + x))) ≤
      2 * t * (alph R A T c j 0 * alph R A T c j 1)) :
    E3 R T c j (fun h a b => if Good S (4 / ρv) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h))
      then 0 else 1) ≤
      8 * (2 * t + e5) + 30 * (√(√ε4 + 200 * T.card * θ) + 150 * T.card * θ) /
        (alph R A T c j 0 * alph R A T c j 1) ^ 2 := by
  set δ := √(√ε4 + 200 * T.card * θ) with hδ
  set α0 := alph R A T c j 0
  set α1 := alph R A T c j 1
  set m := (α0 * α1) ^ 2 with hm
  have hm0 : 0 < m := by positivity
  have hα0 : 0 ≤ α0 := alph_nonneg R A T c j 0
  have hα1 : 0 ≤ α1 := alph_nonneg R A T c j 1
  have hα0' : α0 ≤ 1 := alph_le_one A T c j 0 (hR0 _).le
  have hα1' : α1 ≤ 1 := alph_le_one A T c j 1 (hR0 _).le
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hPa := regP_center_isDist T (hR0 j).le (aC c)
  have hP2 := regP_isDist T (hR0 (j + 2)).le
  set err := 2 * (50 * T.card * R (j + 3) / R j) + 50 * T.card * R (j + 3) / R (j + 2)
    with herr
  have hθ1' : θ ≤ 1 := by linarith
  have herr' : err ≤ 150 * T.card * θ := by
    have r1 := ratio_le_sc hR0 hRk hθ0 hθ1' (50 * T.card) (by positivity) (show j < j + 3 by omega)
    have r2 := ratio_le_sc hR0 hRk hθ0 hθ1' (50 * T.card) (by positivity)
      (show j + 2 < j + 3 by omega)
    linarith
  have herr0 : 0 ≤ err := by
    have := (hR0 (j + 3)).le; have := hR0 j; have := hR0 (j + 2); positivity
  -- pointwise bound
  have hpt : ∀ h a b, (if Good S (4 / ρv) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h)) then (0 : ℝ)
      else 1) ≤ 2 / m * (|EIf R A T c j h a b - m| +
        ∑ x, regP T (R (j + 2)) x * Qs S ρv ξ ξ' A c h a b x) := by
    intro h a b
    refine ind_le_ratio hm0 ?_ fun hb => sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (Iq_le_Qs S ρv ξ ξ' A c h a b x hb) (regP_nonneg _ _)
    exact sum_nonneg fun x _ => mul_nonneg (regP_nonneg _ _) (Qs_nonneg _ _ _ _ _ _ _ _ _ _)
  -- the expected size of the very bad set
  have hEY : ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x * Y1 S ρv ξ ξ' A c a x ≤
      α0 * α1 * (2 * t + e5) + δ := by
    have hJ := (wavg_abs_le_sqrt hPa.1 hPa.2 (fun a => g12 R A T c j a - α0 * α1)).trans
      (Real.sqrt_le_sqrt (g12_conc hR0 hRk hθ0 hθ1 hPR))
    have hpt2 : ∀ a, ∑ x, regP T (R (j + 2)) x * Y1 S ρv ξ ξ' A c a x ≤
        (α0 * α1) * (if a ∈ Gd then 0 else 1) + (2 * t * (α0 * α1) +
          |g12 R A T c j a - α0 * α1|) := by
      intro a
      by_cases ha : a ∈ Gd
      · rw [if_pos ha, mul_zero, zero_add]
        have := hGd2 a ha
        have := abs_nonneg (g12 R A T c j a - α0 * α1)
        unfold Y1; linarith
      · rw [if_neg ha, mul_one]
        have h1 : ∑ x, regP T (R (j + 2)) x * Y1 S ρv ξ ξ' A c a x ≤ g12 R A T c j a :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right (I12_nonneg _ _ _) (vb_le_one _ _ _)) (regP_nonneg _ _)
        have := le_abs_self (g12 R A T c j a - α0 * α1)
        have : 0 ≤ 2 * t * (α0 * α1) := by positivity
        linarith
    calc _ ≤ ∑ a, regP T (R j) (a - aC c) * ((α0 * α1) * (if a ∈ Gd then 0 else 1) +
          (2 * t * (α0 * α1) + |g12 R A T c j a - α0 * α1|)) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt2 a) (regP_nonneg _ _)
      _ = (α0 * α1) * ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) +
          (2 * t * (α0 * α1) + ∑ a, regP T (R j) (a - aC c) * |g12 R A T c j a - α0 * α1|) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
          rw [← sum_mul, hPa.2, one_mul]
          congr 1; exact sum_congr rfl fun _ _ => by ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hGd1 (mul_nonneg hα0 hα1)
          nlinarith
  -- the factored penalty
  have hPF := pf_bound hR0 hRk hθ0 hθ1 hPR (Y1 S ρv ξ ξ' A c) (Y1_nonneg S ρv ξ ξ' A c)
    (Y1_le_one S ρv ξ ξ' A c)
  set PF := ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
    (Y1 S ρv ξ ξ' A c a x * (G1f R A T c j x * H0f R A T c j x)) with hPFdef
  have hPF' : PF ≤ m * (2 * t + e5) + 3 * δ := by
    have i1 := mul_le_mul_of_nonneg_left hEY hα0
    have i2 := mul_le_mul_of_nonneg_left i1 hα1
    have e : α1 * (α0 * (α0 * α1 * (2 * t + e5) + δ)) = m * (2 * t + e5) + α1 * α0 * δ := by
      rw [hm]; ring
    have h3 : α1 * δ ≤ δ := mul_le_of_le_one_left hδ0 hα1'
    have h4 : α1 * α0 * δ ≤ δ := mul_le_of_le_one_left hδ0 (mul_le_one₀ hα1' hα0 hα0')
    have e2 : α1 * (α0 * ∑ a, regP T (R j) (a - aC c) * ∑ x, regP T (R (j + 2)) x *
        Y1 S ρv ξ ξ' A c a x + δ) = α1 * (α0 * ∑ a, regP T (R j) (a - aC c) *
        ∑ x, regP T (R (j + 2)) x * Y1 S ρv ξ ξ' A c a x) + α1 * δ := by ring
    rw [e2] at hPF
    linarith
  -- splitting the penalty
  set F1 : ZMod p → ZMod p → ZMod p → ℝ := fun h a b => ∑ x, regP T (R (j + 2)) x *
    (ind (A 0) (b - (cent c 1 + x)) * ind (A 1) (cent c 1 + x + h) * Y1 S ρv ξ ξ' A c a x)
    with hF1
  set F3 : ZMod p → ZMod p → ZMod p → ℝ := fun h a b => ∑ x, regP T (R (j + 2)) x *
    (ind (A 0) (b - (cent c 1 + x)) * ind (A 1) (cent c 1 + x) *
      Y1 S ρv ξ ξ' A c (a + h) (x + h)) with hF3
  have hsplit : E3 R T c j (fun h a b => ∑ x, regP T (R (j + 2)) x * Qs S ρv ξ ξ' A c h a b x) =
      E3 R T c j F1 + E3 R T c j (fun h a b => F1 h b a) +
        (E3 R T c j F3 + E3 R T c j (fun h a b => F3 h b a)) := by
    rw [← E3_add, ← E3_add, ← E3_add]
    congr 1; funext h a b
    simp only [hF1, hF3, Qs, mul_add, sum_add_distrib]
  have hE1 : E3 R T c j F1 = PF := pen1_eq R A T c j (Y1 S ρv ξ ξ' A c)
  have hE3 : E3 R T c j F3 ≤ PF + err :=
    pen3_le hR0 hRk hθ0 hθ1 A T c j (Y1 S ρv ξ ξ' A c) (Y1_nonneg S ρv ξ ξ' A c)
      (Y1_le_one S ρv ξ ξ' A c)
  have hEI : E3 R T c j (fun h a b => |EIf R A T c j h a b - m|) ≤ 3 * δ :=
    ei_bound hR0 hRk hθ0 hθ1 hPR
  have key : E3 R T c j (fun h a b => if Good S (4 / ρv) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h))
      then 0 else 1) ≤ 2 / m * (3 * δ + 4 * (m * (2 * t + e5) + 3 * δ) + 2 * err) := by
    refine (E3_mono R T c j hpt).trans ?_
    rw [E3_smul, E3_add, hsplit, E3_swap R T c j F1, E3_swap R T c j F3, hE1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  refine key.trans ?_
  have e : 2 / m * (3 * δ + 4 * (m * (2 * t + e5) + 3 * δ) + 2 * err) =
      8 * (2 * t + e5) + (30 * δ + 4 * err) / m := by
    field_simp; ring
  rw [e]
  have : (30 * δ + 4 * err) / m ≤ 30 * (δ + 150 * T.card * θ) / m :=
    div_le_div_of_nonneg_right (by linarith) hm0.le
  linarith

end pordo

end

end GT
end File_GT_U3S6d

open Finset KM
open scoped ComplexConjugate
open Classical
open GT in
theorem solution {p : ℕ} [NeZero p] {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)} {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ} (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4) (S : Finset (ZMod p)) (ρv : ℝ) (ξ ξ' : ZMod p → ZMod p) (Gd : Finset (ZMod p))
    {t e5 : ℝ} (ht : 0 ≤ t) (hpos : 0 < alph R A T c j 0 * alph R A T c j 1)
    (hGd1 : ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) ≤ e5)
    (hGd2 : ∀ a ∈ Gd, ∑ x, regP T (R (j + 2)) x * (I12 A a (cent c 1 + x) *
      vb S ρv (ξ' a - ξ (a - (cent c 1 + x)) - ξ (cent c 1 + x))) ≤
      2 * t * (alph R A T c j 0 * alph R A T c j 1)) :
    E3 R T c j (fun h a b => if Good S (4 / ρv) (ξ' a - ξ' (a + h) - ξ' b + ξ' (b + h))
      then 0 else 1) ≤
      8 * (2 * t + e5) + 30 * (√(√ε4 + 200 * T.card * θ) + 150 * T.card * θ) /
        (alph R A T c j 0 * alph R A T c j 1) ^ 2 :=
  @GT.pordo p _ R θ hR0 hRk hθ0 hθ1 T A c j ε4 hPR S ρv ξ ξ' Gd t e5 ht hpos hGd1 hGd2

