-- Prove2me | solution 1 for GT.u3_step3
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:52:56.745732+00:00
-- url     : https://prove2.me/submissions/dbd4338e-3b8d-460c-9532-add2e90f834d

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

lemma cn_sub_le (a b : ZMod N) : cn (a - b) ≤ cn a + cn b := by
  rw [sub_eq_add_neg]; exact (cn_add_le _ _).trans (by rw [cn_neg])

lemma cn_le_half (z : ZMod N) : cn z ≤ 1 / 2 := by
  have := AddCircle.norm_le_half_period (1 : ℝ) (x := ZMod.toAddCircle z) one_ne_zero
  simpa [cn] using this

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

lemma bohr_eq_univ (h : 1 / 2 ≤ ρ) : bohr Γ ρ = univ := by
  ext x; simp only [mem_bohr, mem_univ, iff_true]
  exact fun γ _ => (cn_le_half _).trans h

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

theorem card_bohr_ge (Γ : Finset (ZMod N)) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    (N : ℝ) * (ρ / 2) ^ Γ.card ≤ (bohr Γ ρ).card := by
  have h := card_bohr_le Γ (ρ := 1 / 2) hρ hρ1
  rw [bohr_eq_univ le_rfl, card_univ, ZMod.card] at h
  have e : 4 * (1 / 2 : ℝ) / ρ = (ρ / 2)⁻¹ := by field_simp; norm_num
  rw [e, inv_pow] at h
  have hpos : 0 < (ρ / 2) ^ Γ.card := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ hpos] at h
  linarith

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

/-- Point-mass bound for regular distributions (the bound (4.2) of Green–Tao). -/
lemma regP_le (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (a : ZMod N) :
    regP Γ ρ a ≤ 1 / (N * (ρ / 4) ^ Γ.card) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hbound : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, mu (bohr Γ (t * ρ)) a ≤ 1 / (N * (ρ / 4) ^ Γ.card) := by
    intro t ht
    have htρ : 0 < t * ρ := mul_pos (by linarith [ht.1]) hρ
    have hcard : (N : ℝ) * (ρ / 4) ^ Γ.card ≤ (bohr Γ (t * ρ)).card := by
      rcases le_or_gt (t * ρ) (1 / 2) with hle | hgt
      · refine le_trans ?_ (card_bohr_ge Γ htρ hle)
        apply mul_le_mul_of_nonneg_left _ hN.le
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [ht.1]
      · rw [bohr_eq_univ hgt.le, card_univ, ZMod.card]
        have : (ρ / 4) ^ Γ.card ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
        nlinarith
    refine (mu_le _ a).trans ?_
    rw [one_div]
    exact inv_anti₀ (by positivity) hcard
  unfold regP
  have := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (intervalIntegrable_mu_bohr Γ hρ.le a _ _) intervalIntegrable_const hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

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

@[simp] lemma ech_zero : ech (0 : ZMod N) = 1 := AddChar.map_zero_eq_one _

lemma ech_neg (a : ZMod N) : ech (-a) = conj (ech a) := AddChar.map_neg_eq_conj _ _

@[simp] lemma norm_ech (a : ZMod N) : ‖ech a‖ = 1 := AddChar.norm_apply _ _

lemma ech_sub (a b : ZMod N) : ech (a - b) = ech a * ech (-b) := by
  rw [sub_eq_add_neg, ech_add]

lemma sum_ech_mul (γ : ZMod N) : ∑ x, ech (x * γ) = if γ = 0 then (N : ℂ) else 0 := by
  have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod N) ℂ)) γ
    (ZMod.isPrimitive_stdAddChar N)
  unfold ech; rw [this]; split_ifs <;> simp [ZMod.card]

end

end KM
end File_KM_Fourier

section File_GT_Jackson
/-!
# The Jackson kernel on `ZMod N`

For `M ≥ 1` and `N ≥ 2M`, the kernel `J(z) = N |∑_{a<M} e(az/N)|^4 / ∑_z |…|^4` on `ZMod N`
is non-negative, has total mass `N`, first moment `∑ J(z) ‖z/N‖ ≤ N/M`, and is a
non-negative combination of characters with frequencies `a + b - c - d` (`a, b, c, d < M`),
with total coefficient mass `≤ 2M`.
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N]

lemma ech_eq_exp_sc (z : ZMod N) :
    ech z = Complex.exp (Complex.I * ((2 * Real.pi * sc z : ℝ) : ℂ)) := by
  unfold ech
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold sc
  set u : ℝ := (z.val : ℝ) / N
  have : 2 * ↑Real.pi * Complex.I * ↑z.val / ↑N =
      Complex.I * ((2 * Real.pi * (u - round u) : ℝ) : ℂ) +
        (round u : ℤ) * (2 * Real.pi * Complex.I) := by
    simp only [u]; push_cast; field_simp; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `4 ‖z/N‖ ≤ |e(z/N) - 1|`. -/
lemma four_cn_le (z : ZMod N) : 4 * cn z ≤ ‖ech z - 1‖ := by
  rw [ech_eq_exp_sc, Complex.norm_exp_I_mul_ofReal_sub_one, cn_eq_abs_sc]
  have hs : |sc z| ≤ 1 / 2 := by rw [← cn_eq_abs_sc]; exact cn_le_half z
  have hx0 : 0 ≤ Real.pi * |sc z| := by positivity
  have hx1 : Real.pi * |sc z| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hx0 hx1
  have e : 2 / Real.pi * (Real.pi * |sc z|) = 2 * |sc z| := by field_simp
  rw [e] at hsin
  have habs : |Real.sin (2 * Real.pi * sc z / 2)| = Real.sin (Real.pi * |sc z|) := by
    rw [show 2 * Real.pi * sc z / 2 = Real.pi * sc z by ring]
    rcases le_or_gt 0 (sc z) with h | h
    · have h1 : sc z ≤ 1 / 2 := le_trans (le_abs_self _) hs
      rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos]))]
    · have h1 : -sc z ≤ 1 / 2 := le_trans (neg_le_abs _) hs
      rw [abs_of_neg h, show Real.pi * sc z = -(Real.pi * -sc z) by ring, Real.sin_neg,
        abs_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos]))]
  rw [Real.norm_eq_abs, abs_mul, abs_two, habs]
  linarith

/-- Orthogonality for small integer frequencies. -/
lemma sum_ech_int (m : ℤ) (hm : |m| < N) :
    ∑ z : ZMod N, ech ((m : ZMod N) * z) = if m = 0 then (N : ℂ) else 0 := by
  have h := sum_ech_mul (N := N) (m : ZMod N)
  have e : ∑ z : ZMod N, ech ((m : ZMod N) * z) = ∑ z : ZMod N, ech (z * (m : ZMod N)) :=
    Finset.sum_congr rfl fun z _ => by rw [mul_comm]
  rw [e, h]
  have : ((m : ZMod N) = 0) ↔ m = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro hd
      by_contra h0
      have := Int.le_of_dvd (abs_pos.mpr h0) ((dvd_abs _ _).mpr hd)
      linarith
    · rintro rfl; exact dvd_zero _
  simp only [this]

/-- The Dirichlet-type sum `S(z) = ∑_{a<M} e(az/N)`. -/
def dS (M : ℕ) (z : ZMod N) : ℂ := ∑ a : Fin M, ech (((a : ℕ) : ZMod N) * z)

lemma normSq_dS (M : ℕ) (z : ZMod N) :
    ((‖dS M z‖ ^ 2 : ℝ) : ℂ) = ∑ a : Fin M, ∑ b : Fin M, ech ((((a : ℤ) - b : ℤ) : ZMod N) * z) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', dS, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← ech_neg, ← ech_add]
  congr 1; push_cast; ring

lemma sum_normSq_dS {M : ℕ} (hM : M ≤ N) : ∑ z : ZMod N, ‖dS M z‖ ^ 2 = N * M := by
  have key : ((∑ z : ZMod N, ‖dS M z‖ ^ 2 : ℝ) : ℂ) = ((N * M : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [normSq_dS]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    have : ∀ a b : Fin M, ∑ z : ZMod N, ech ((((a : ℤ) - b : ℤ) : ZMod N) * z) =
        if a = b then (N : ℂ) else 0 := by
      intro a b
      rw [sum_ech_int]
      · simp only [sub_eq_zero, Nat.cast_inj, Fin.val_inj]
      · have := a.isLt; have := b.isLt
        rw [abs_lt]; constructor <;> omega
    simp_rw [this]
    simp [Finset.sum_ite_eq]
    ring
  exact_mod_cast key

lemma dS_sq_mul_conj (M : ℕ) (z : ZMod N) :
    (dS M z) ^ 2 * conj (dS (2 * M - 1) z) =
      ∑ a : Fin M, ∑ b : Fin M, ∑ n : Fin (2 * M - 1),
        ech ((((a : ℤ) + b - n : ℤ) : ZMod N) * z) := by
  simp only [dS]
  rw [sq, Finset.sum_mul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← ech_neg, ← ech_add, ← ech_add]
  congr 1; push_cast; ring

lemma sum_dS_sq_mul_conj {M : ℕ} (hM : 1 ≤ M) (h2 : 2 * M ≤ N) :
    ∑ z : ZMod N, (dS M z) ^ 2 * conj (dS (2 * M - 1) z) = N * M ^ 2 := by
  simp_rw [dS_sq_mul_conj]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  have hin : ∀ (a b : Fin M) (n : Fin (2 * M - 1)),
      ∑ z : ZMod N, ech ((((a : ℤ) + b - n : ℤ) : ZMod N) * z) =
        if (n : ℕ) = a + b then (N : ℂ) else 0 := by
    intro a b n
    rw [sum_ech_int]
    · congr 1
      apply propext
      constructor
      · intro h; omega
      · intro h; omega
    · have := a.isLt; have := b.isLt; have := n.isLt
      rw [abs_lt]; constructor <;> omega
  simp_rw [hin]
  have hone : ∀ a b : Fin M, ∑ n : Fin (2 * M - 1), (if (n : ℕ) = a + b then (N : ℂ) else 0) =
      N := by
    intro a b
    have hlt : (a : ℕ) + b < 2 * M - 1 := by have := a.isLt; have := b.isLt; omega
    rw [Finset.sum_eq_single ⟨a + b, hlt⟩]
    · simp
    · intro n _ hn
      rw [if_neg]
      intro h; apply hn; ext; exact h
    · simp
  simp_rw [hone]
  simp [Finset.sum_const, Finset.card_univ]
  ring

/-- `∑_z |S(z)|^4`. -/
def Z4 (N M : ℕ) [NeZero N] : ℝ := ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 4

lemma Z4_ge {M : ℕ} (hM : 1 ≤ M) (h2 : 2 * M ≤ N) : (N : ℝ) * M ^ 3 / 2 ≤ Z4 N M := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hT : ∑ z : ZMod N, ‖dS (2 * M - 1) z‖ ^ 2 = N * ((2 * M - 1 : ℕ) : ℝ) :=
    sum_normSq_dS (by omega)
  have h1 : (N : ℝ) * M ^ 2 ≤ ∑ z : ZMod N, ‖dS M z‖ ^ 2 * ‖dS (2 * M - 1) z‖ := by
    have := sum_dS_sq_mul_conj (N := N) hM h2
    have h := norm_sum_le (univ : Finset (ZMod N))
      (fun z => (dS M z) ^ 2 * conj (dS (2 * M - 1) z))
    rw [this] at h
    have e : ‖((N : ℂ) * (M : ℂ) ^ 2)‖ = (N : ℝ) * M ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    rw [e] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_))
    rw [norm_mul, norm_pow, Complex.norm_conj]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod N))
    (fun z => ‖dS (N := N) M z‖ ^ 2) (fun z => ‖dS (N := N) (2 * M - 1) z‖)
  rw [hT] at hcs
  have e4 : ∑ z : ZMod N, (‖dS (N := N) M z‖ ^ 2) ^ 2 = Z4 N M := by
    unfold Z4; refine Finset.sum_congr rfl fun z _ => by ring
  rw [e4] at hcs
  have hsq : ((N : ℝ) * M ^ 2) ^ 2 ≤ Z4 N M * (N * ((2 * M - 1 : ℕ) : ℝ)) :=
    le_trans (pow_le_pow_left₀ (by positivity) h1 2) hcs
  have hcast : ((2 * M - 1 : ℕ) : ℝ) = 2 * M - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hsq
  have hZ0 : 0 ≤ Z4 N M := Finset.sum_nonneg fun z _ => by positivity
  -- `N² M⁴ ≤ Z4 · N (2M - 1)` gives `Z4 ≥ N M³ / 2`.
  by_contra hlt
  push_neg at hlt
  have : Z4 N M * (N * (2 * M - 1)) < (N : ℝ) * M ^ 3 / 2 * (N * (2 * M - 1)) :=
    mul_lt_mul_of_pos_right hlt (by nlinarith)
  nlinarith

lemma dS_mul_one_sub (M : ℕ) (z : ZMod N) :
    dS M z * (1 - ech z) = 1 - ech ((M : ZMod N) * z) := by
  unfold dS
  rw [Fin.sum_univ_eq_sum_range (fun a => ech (((a : ℕ) : ZMod N) * z)), Finset.sum_mul]
  have : ∀ a ∈ Finset.range M, ech (((a : ℕ) : ZMod N) * z) * (1 - ech z) =
      ech (((a : ℕ) : ZMod N) * z) - ech ((((a + 1 : ℕ)) : ZMod N) * z) := by
    intro a _
    rw [mul_sub, mul_one, ← ech_add]; congr 2; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub']
  simp

lemma norm_dS_mul_le (M : ℕ) (z : ZMod N) : ‖dS M z‖ * ‖1 - ech z‖ ≤ 2 := by
  rw [← norm_mul, dS_mul_one_sub]
  refine (norm_sub_le _ _).trans ?_
  simp; norm_num

/-- The Jackson kernel. -/
def jk (N M : ℕ) [NeZero N] (z : ZMod N) : ℝ := ‖dS (N := N) M z‖ ^ 4 * N / Z4 N M

lemma jk_nonneg (M : ℕ) (z : ZMod N) : 0 ≤ jk N M z := by
  unfold jk
  have : 0 ≤ Z4 N M := Finset.sum_nonneg fun z _ => by positivity
  positivity

lemma sum_jk {M : ℕ} (hM : 1 ≤ M) (h2 : 2 * M ≤ N) : ∑ z : ZMod N, jk N M z = N := by
  have hZ : 0 < Z4 N M := by
    have := Z4_ge (N := N) hM h2
    have : (0 : ℝ) < N * M ^ 3 / 2 := by
      have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      have : (1 : ℝ) ≤ M := by exact_mod_cast hM
      positivity
    linarith
  unfold jk
  rw [← Finset.sum_div, ← Finset.sum_mul]
  change Z4 N M * N / Z4 N M = N
  field_simp

lemma sum_jk_cn_le {M : ℕ} (hM : 1 ≤ M) (h2 : 2 * M ≤ N) :
    ∑ z : ZMod N, jk N M z * cn z ≤ N / M := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hZge := Z4_ge (N := N) hM h2
  have hZ : 0 < Z4 N M := lt_of_lt_of_le (by positivity) hZge
  -- `∑ |S|^4 cn² ≤ N M / 4`
  have h1 : ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z ^ 2 ≤ N * M / 4 := by
    have hpt : ∀ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z ^ 2 ≤ ‖dS (N := N) M z‖ ^ 2 / 4 := by
      intro z
      have h4 := four_cn_le z
      have hc := cn_nonneg z
      have hd := norm_dS_mul_le M z
      have e : ‖ech z - 1‖ = ‖1 - ech z‖ := norm_sub_rev _ _
      rw [e] at h4
      have hS := norm_nonneg (dS (N := N) M z)
      have : ‖dS (N := N) M z‖ * (4 * cn z) ≤ 2 := le_trans (mul_le_mul_of_nonneg_left h4 hS) hd
      have h5 : ‖dS (N := N) M z‖ * cn z ≤ 1 / 2 := by linarith
      have h6 : (‖dS (N := N) M z‖ * cn z) ^ 2 ≤ 1 / 4 := by
        nlinarith [mul_nonneg hS hc]
      calc ‖dS (N := N) M z‖ ^ 4 * cn z ^ 2 = ‖dS (N := N) M z‖ ^ 2 * (‖dS (N := N) M z‖ * cn z) ^ 2 := by
            ring
        _ ≤ ‖dS (N := N) M z‖ ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = _ := by ring
    calc ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z ^ 2 ≤ ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 2 / 4 :=
          Finset.sum_le_sum fun z _ => hpt z
      _ = N * M / 4 := by rw [← Finset.sum_div, sum_normSq_dS (by omega)]
  -- AM-GM: `cn ≤ 1/(2M) + M cn² / 2`
  have hpt2 : ∀ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z ≤
      ‖dS (N := N) M z‖ ^ 4 / (2 * M) + M / 2 * (‖dS (N := N) M z‖ ^ 4 * cn z ^ 2) := by
    intro z
    have hS : 0 ≤ ‖dS (N := N) M z‖ ^ 4 := by positivity
    have : cn z ≤ 1 / (2 * M) + M / 2 * cn z ^ 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (M * cn z - 1)]
    calc ‖dS (N := N) M z‖ ^ 4 * cn z ≤ ‖dS (N := N) M z‖ ^ 4 * (1 / (2 * M) + M / 2 * cn z ^ 2) :=
          mul_le_mul_of_nonneg_left this hS
      _ = _ := by ring
  have h3 : ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z ≤ Z4 N M / (2 * M) + M / 2 * (N * M / 4) := by
    calc ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z
        ≤ ∑ z : ZMod N, (‖dS (N := N) M z‖ ^ 4 / (2 * M) +
            M / 2 * (‖dS (N := N) M z‖ ^ 4 * cn z ^ 2)) := Finset.sum_le_sum fun z _ => hpt2 z
      _ = Z4 N M / (2 * M) + M / 2 * ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]; rfl
      _ ≤ Z4 N M / (2 * M) + M / 2 * (N * M / 4) := by
          gcongr
  have e : ∑ z : ZMod N, jk N M z * cn z = N / Z4 N M * ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z := by
    unfold jk; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => by ring
  rw [e]
  calc N / Z4 N M * ∑ z : ZMod N, ‖dS (N := N) M z‖ ^ 4 * cn z
      ≤ N / Z4 N M * (Z4 N M / (2 * M) + M / 2 * (N * M / 4)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = N / (2 * M) + N ^ 2 * M ^ 2 / (8 * Z4 N M) := by field_simp; ring
    _ ≤ N / (2 * M) + N / (4 * M) := by
        have : (N : ℝ) ^ 2 * M ^ 2 / (8 * Z4 N M) ≤ N / (4 * M) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hZge (by positivity : (0 : ℝ) ≤ N * M * 8)]
        linarith
    _ ≤ N / M := by
        have e2 : (N : ℝ) / (2 * M) + N / (4 * M) = 3 / 4 * (N / M) := by field_simp; ring
        rw [e2]
        nlinarith [div_nonneg hN.le (by positivity : (0 : ℝ) ≤ M)]

/-- The Fourier expansion of the Jackson kernel. -/
lemma jk_expand (M : ℕ) (z : ZMod N) :
    ((jk N M z : ℝ) : ℂ) = ((N / Z4 N M : ℝ) : ℂ) *
      ∑ q : Fin M × Fin M × Fin M × Fin M,
        ech ((((q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2 : ℤ) : ZMod N) * z) := by
  have h4 : ((‖dS (N := N) M z‖ ^ 4 : ℝ) : ℂ) = ((‖dS (N := N) M z‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
    push_cast; ring
  unfold jk
  rw [show ‖dS (N := N) M z‖ ^ 4 * N / Z4 N M = N / Z4 N M * ‖dS (N := N) M z‖ ^ 4 by ring]
  rw [Complex.ofReal_mul, h4, normSq_dS, sq, Finset.sum_mul_sum]
  congr 1
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [← ech_add]; congr 1; push_cast; ring

lemma jk_mass {M : ℕ} (hM : 1 ≤ M) (h2 : 2 * M ≤ N) :
    N / Z4 N M * (M : ℝ) ^ 4 ≤ 2 * M := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hZge := Z4_ge (N := N) hM h2
  have hZ : 0 < Z4 N M := lt_of_lt_of_le (by positivity) hZge
  rw [div_mul_eq_mul_div, div_le_iff₀ hZ]
  nlinarith [mul_le_mul_of_nonneg_left hZge (by positivity : (0 : ℝ) ≤ 2 * M)]

end

end GT
end File_GT_Jackson

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

lemma ech_zero' : ech (0 : ZMod N) = 1 := AddChar.map_zero_eq_one _

lemma ech_sum {ι : Type*} (s : Finset ι) (a : ι → ZMod N) :
    ech (∑ i ∈ s, a i) = ∏ i ∈ s, ech (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ech_zero']
  | insert x s hx ih => rw [sum_insert hx, prod_insert hx, ech_add, ih]

lemma norm_ech (z : ZMod N) : ‖ech z‖ = 1 := by
  unfold ech; simp

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The pairing `∑ᵢ mᵢ gᵢ` of an integer frequency with a grid point. -/
def zdot (m : κ → ℤ) (g : κ → ZMod N) : ZMod N := ∑ i, (m i : ZMod N) * g i

lemma zdot_sub (m : κ → ℤ) (g h : κ → ZMod N) : zdot m (g - h) = zdot m g - zdot m h := by
  simp [zdot, mul_sub, sum_sub_distrib]

lemma zdot_zero_left (g : κ → ZMod N) : zdot (0 : κ → ℤ) g = 0 := by simp [zdot]

/-- The frequency `a + b - c - d` of a quadruple. -/
def qm {M : ℕ} (q : Fin M × Fin M × Fin M × Fin M) : ℤ :=
  (q.1 : ℤ) + q.2.1 - q.2.2.1 - q.2.2.2

lemma abs_qm_lt {M : ℕ} (q : Fin M × Fin M × Fin M × Fin M) : |qm q| < 2 * M := by
  have h1 := q.1.isLt; have h2 := q.2.1.isLt; have h3 := q.2.2.1.isLt; have h4 := q.2.2.2.isLt
  unfold qm; rw [abs_lt]; constructor <;> omega

/-- The product Jackson kernel on `(ZMod N)^κ`. -/
def gK (M : κ → ℕ) (g : κ → ZMod N) : ℝ := ∏ i, jk N (M i) (g i)

lemma gK_nonneg (M : κ → ℕ) (g : κ → ZMod N) : 0 ≤ gK M g :=
  prod_nonneg fun i _ => jk_nonneg (M i) _

lemma sum_gK {M : κ → ℕ} (hM : ∀ i, 1 ≤ M i) (h2 : ∀ i, 2 * M i ≤ N) :
    ∑ g : κ → ZMod N, gK M g = (N : ℝ) ^ Fintype.card κ := by
  unfold gK
  rw [← Fintype.prod_sum (fun (i : κ) z => jk N (M i) z)]
  simp [sum_jk (hM _) (h2 _)]

lemma sum_gK_cn {M : κ → ℕ} (hM : ∀ i, 1 ≤ M i) (h2 : ∀ i, 2 * M i ≤ N) (i : κ) :
    ∑ g : κ → ZMod N, gK M g * cn (g i) ≤ (N : ℝ) ^ Fintype.card κ / M i := by
  have e : ∀ g : κ → ZMod N, gK M g * cn (g i) =
      ∏ j, (fun j z => if j = i then jk N (M j) z * cn z else jk N (M j) z) j (g j) := by
    intro g
    unfold gK
    rw [← mul_prod_erase univ (fun j => jk N (M j) (g j)) (mem_univ i),
      ← mul_prod_erase univ _ (mem_univ i)]
    simp only [if_pos rfl]
    rw [mul_right_comm]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    rw [if_neg (ne_of_mem_erase hj)]
  simp_rw [e]
  have hps := Fintype.prod_sum (fun j (z : ZMod N) => if j = i then jk N (M j) z * cn z else jk N (M j) z)
  try simp only at hps
  rw [← hps]
  rw [← mul_prod_erase univ _ (mem_univ i)]
  simp only [if_pos rfl]
  have hrest : ∏ j ∈ univ.erase i, ∑ z : ZMod N, (if j = i then jk N (M j) z * cn z else jk N (M j) z)
      = (N : ℝ) ^ (Fintype.card κ - 1) := by
    rw [prod_congr rfl fun j hj => by rw [sum_congr rfl fun z _ => if_neg (ne_of_mem_erase hj)]]
    rw [prod_congr rfl fun j _ => sum_jk (hM j) (h2 j), prod_const, card_erase_of_mem (mem_univ i),
      card_univ]
  rw [hrest]
  have hc : Fintype.card κ = (Fintype.card κ - 1) + 1 := by
    have := Fintype.card_pos_iff.mpr ⟨i⟩; omega
  have hN : (0 : ℝ) ≤ (N : ℝ) ^ (Fintype.card κ - 1) := by positivity
  calc (∑ z : ZMod N, jk N (M i) z * cn z) * (N : ℝ) ^ (Fintype.card κ - 1)
      ≤ (N / M i) * (N : ℝ) ^ (Fintype.card κ - 1) :=
        mul_le_mul_of_nonneg_right (sum_jk_cn_le (hM i) (h2 i)) hN
    _ = (N : ℝ) ^ Fintype.card κ / M i := by
        conv_rhs => rw [hc, pow_succ]
        ring

/-- The smoothing of `f` by the product Jackson kernel. -/
def smooth (M : κ → ℕ) (f : (κ → ZMod N) → ℝ) (y : κ → ZMod N) : ℝ :=
  ((N : ℝ) ^ Fintype.card κ)⁻¹ * ∑ g, gK M g * f (y - g)

lemma abs_sub_smooth {M : κ → ℕ} (hM : ∀ i, 1 ≤ M i) (h2 : ∀ i, 2 * M i ≤ N) {W : κ → ℝ}
    (hW : ∀ i, 0 ≤ W i)
    {f : (κ → ZMod N) → ℝ} (hf : ∀ y h, |f y - f (y - h)| ≤ ∑ i, W i * cn (h i))
    (y : κ → ZMod N) : |f y - smooth M f y| ≤ ∑ i, W i / M i := by
  have hNd : (0 : ℝ) < (N : ℝ) ^ Fintype.card κ := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have e : f y - smooth M f y =
      ((N : ℝ) ^ Fintype.card κ)⁻¹ * ∑ g, gK M g * (f y - f (y - g)) := by
    unfold smooth
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_gK hM h2]
    field_simp
  rw [e, abs_mul, abs_inv, abs_of_pos hNd]
  have hs : |∑ g, gK M g * (f y - f (y - g))| ≤
      ∑ i, W i * ∑ g : κ → ZMod N, gK M g * cn (g i) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_le_sum fun g _ => ?_
    rw [abs_mul, abs_of_nonneg (gK_nonneg M g)]
    calc gK M g * |f y - f (y - g)| ≤ gK M g * (∑ i, W i * cn (g i)) :=
          mul_le_mul_of_nonneg_left (hf y g) (gK_nonneg M g)
      _ = ∑ i, W i * (gK M g * cn (g i)) := by rw [mul_sum]; ring_nf
  have hs2 : ∑ i, W i * ∑ g : κ → ZMod N, gK M g * cn (g i) ≤
      ∑ i, W i * ((N : ℝ) ^ Fintype.card κ / M i) :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (sum_gK_cn hM h2 i) (hW i)
  calc ((N : ℝ) ^ Fintype.card κ)⁻¹ * |∑ g, gK M g * (f y - f (y - g))|
      ≤ ((N : ℝ) ^ Fintype.card κ)⁻¹ * ∑ i, W i * ((N : ℝ) ^ Fintype.card κ / M i) :=
        mul_le_mul_of_nonneg_left (hs.trans hs2) (by positivity)
    _ = ∑ i, W i / M i := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        field_simp

/-- The grid Fourier coefficient `N^{-|κ|} ∑_g f(g) e(-m·g/N)`. -/
def fhat (f : (κ → ZMod N) → ℝ) (m : κ → ℤ) : ℂ :=
  ((N : ℂ) ^ Fintype.card κ)⁻¹ * ∑ g, (f g : ℂ) * ech (-zdot m g)

lemma fhat_zero {f : (κ → ZMod N) → ℝ} (hf : ∑ g, f g = 0) : fhat f 0 = 0 := by
  unfold fhat
  simp only [zdot_zero_left, neg_zero, ech_zero', mul_one]
  rw [← Complex.ofReal_sum, hf]; simp

lemma norm_fhat_le {f : (κ → ZMod N) → ℝ} {B : ℝ} (hB : ∀ g, |f g| ≤ B) (m : κ → ℤ) :
    ‖fhat f m‖ ≤ B := by
  unfold fhat
  have hNd : (0 : ℝ) < (N : ℝ) ^ Fintype.card κ := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have : ‖∑ g, (f g : ℂ) * ech (-zdot m g)‖ ≤ (N : ℝ) ^ Fintype.card κ * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ g, ‖(f g : ℂ) * ech (-zdot m g)‖ ≤ ∑ _g : κ → ZMod N, B :=
          sum_le_sum fun g _ => (by
            rw [norm_mul, norm_ech, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hB g)
      _ = _ := by simp [Fintype.card_fun]
  calc ((N : ℝ) ^ Fintype.card κ)⁻¹ * ‖∑ g, (f g : ℂ) * ech (-zdot m g)‖
      ≤ ((N : ℝ) ^ Fintype.card κ)⁻¹ * ((N : ℝ) ^ Fintype.card κ * B) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = B := by field_simp

/-- Families of quadruples, one quadruple in `Fin (M i)^4` for each coordinate `i`. -/
abbrev Quads (M : κ → ℕ) : Type _ := (i : κ) → Fin (M i) × Fin (M i) × Fin (M i) × Fin (M i)

/-- The frequency vector of a family of quadruples. -/
def mQ {M : κ → ℕ} (Q : Quads M) : κ → ℤ := fun i => qm (Q i)

/-- The normalising constant of the product kernel. -/
def kC (N : ℕ) [NeZero N] (M : κ → ℕ) : ℝ := ∏ i, (N / Z4 N (M i))

lemma gK_expand (M : κ → ℕ) (g : κ → ZMod N) :
    ((gK M g : ℝ) : ℂ) = ((kC N M : ℝ) : ℂ) * ∑ Q : Quads M, ech (zdot (mQ Q) g) := by
  unfold gK kC
  rw [Complex.ofReal_prod, Complex.ofReal_prod]
  simp_rw [jk_expand]
  rw [prod_mul_distrib, Fintype.prod_sum]
  congr 1
  refine sum_congr rfl fun Q _ => ?_
  rw [zdot, ech_sum]
  rfl

lemma sum_shift (m : κ → ℤ) (f : (κ → ZMod N) → ℝ) (y : κ → ZMod N) :
    ∑ g, ech (zdot m g) * (f (y - g) : ℂ) = ech (zdot m y) * ∑ g, (f g : ℂ) * ech (-zdot m g) := by
  rw [mul_sum, ← Equiv.sum_comp (Equiv.subLeft y)]
  refine sum_congr rfl fun g _ => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel, zdot_sub, ech_sub]
  ring

lemma smooth_expand (M : κ → ℕ) (f : (κ → ZMod N) → ℝ) (y : κ → ZMod N) :
    ((smooth M f y : ℝ) : ℂ) = ((kC N M : ℝ) : ℂ) *
      ∑ Q : Quads M, ech (zdot (mQ Q) y) * fhat f (mQ Q) := by
  set c : ℂ := ((kC N M : ℝ) : ℂ)
  set D : ℂ := ((N : ℂ) ^ Fintype.card κ)⁻¹
  unfold smooth fhat
  rw [Complex.ofReal_mul, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, gK_expand]
  have hD : (((N : ℝ) ^ Fintype.card κ)⁻¹ : ℝ) = D := by simp [D]
  rw [hD]
  calc D * ∑ g : κ → ZMod N, c * (∑ Q : Quads M, ech (zdot (mQ Q) g)) * (f (y - g) : ℂ)
      = ∑ Q : Quads M, ∑ g : κ → ZMod N, D * c * (ech (zdot (mQ Q) g) * (f (y - g) : ℂ)) := by
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        exact sum_congr rfl fun Q _ => sum_congr rfl fun g _ => by ring
    _ = ∑ Q : Quads M, D * c * ∑ g : κ → ZMod N, ech (zdot (mQ Q) g) * (f (y - g) : ℂ) := by
        simp only [mul_sum]
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun Q _ => ?_
        rw [sum_shift]
        ring

lemma kC_mass {M : κ → ℕ} (hM : ∀ i, 1 ≤ M i) (h2 : ∀ i, 2 * M i ≤ N) :
    kC N M * (Fintype.card (Quads M) : ℝ) ≤ ∏ i, (2 * M i : ℝ) := by
  unfold kC
  simp only [Fintype.card_pi, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [← prod_mul_distrib]
  refine prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · have hZ : 0 < Z4 N (M i) := by
      have := Z4_ge (N := N) (hM i) (h2 i)
      have : (0 : ℝ) < N * (M i : ℝ) ^ 3 / 2 := by
        have : (1 : ℝ) ≤ M i := by exact_mod_cast hM i
        have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
        positivity
      linarith
    positivity
  · have := jk_mass (N := N) (hM i) (h2 i)
    calc (N : ℝ) / Z4 N (M i) * ((M i : ℝ) * (M i * (M i * M i)))
        = N / Z4 N (M i) * (M i : ℝ) ^ 4 := by ring
      _ ≤ _ := this

/-- **Weyl lemma on the grid.** -/
theorem weyl_grid {M : κ → ℕ} (hM : ∀ i, 1 ≤ M i) (h2 : ∀ i, 2 * M i ≤ N) {W : κ → ℝ}
    {B δ : ℝ} (hW : ∀ i, 0 ≤ W i)
    {f : (κ → ZMod N) → ℝ} (hf : ∀ y h, |f y - f (y - h)| ≤ ∑ i, W i * cn (h i))
    (hB : ∀ g, |f g| ≤ B) (hmean : ∑ g, f g = 0) (hWM : ∑ i, W i / M i < δ / 2)
    {ι : Type*} [Fintype ι] (ω : ι → ℝ) (hω : ∑ j, |ω j| ≤ 1) (y : ι → κ → ZMod N)
    (hδ : δ ≤ |∑ j, ω j * f (y j)|) :
    ∃ k : κ → ℤ, k ≠ 0 ∧ (∀ i, |k i| < 2 * M i) ∧
      δ ≤ 2 * B * (∏ i, (2 * M i : ℝ)) * ‖∑ j, (ω j : ℂ) * ech (zdot k (y j))‖ := by
  by_contra hcon
  push_neg at hcon
  set C : ℝ := kC N M with hC
  set P : ℝ := ∏ i, (2 * M i : ℝ) with hPdef
  set S : (κ → ℤ) → ℂ := fun m => ∑ j, (ω j : ℂ) * ech (zdot m (y j)) with hS
  have hC0 : 0 ≤ C := by
    rw [hC, kC]
    refine prod_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _)
      (sum_nonneg fun z _ => by positivity)
  have hP : 0 < P := prod_pos fun i _ => by
    have : (1 : ℝ) ≤ M i := by exact_mod_cast hM i
    positivity
  have hE0 : 0 ≤ ∑ i, W i / M i := sum_nonneg fun i _ => div_nonneg (hW i) (Nat.cast_nonneg _)
  have hδ0 : 0 ≤ δ := by linarith
  -- the smoothed average
  set T : ℂ := ∑ j, (ω j : ℂ) * ((smooth M f (y j) : ℝ) : ℂ) with hT
  have hTexp : T = (C : ℂ) * ∑ Q : Quads M, fhat f (mQ Q) * S (mQ Q) := by
    rw [hT]
    simp_rw [smooth_expand, hC, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun Q _ => ?_
    rw [hS]; simp only [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  -- each term is small
  have hterm : ∀ Q : Quads M, ‖fhat f (mQ Q) * S (mQ Q)‖ ≤ δ / (2 * P) := by
    intro Q
    by_cases h0 : mQ Q = 0
    · rw [h0, fhat_zero hmean, zero_mul, norm_zero]; positivity
    · have hk := hcon (mQ Q) h0 (fun i => abs_qm_lt (Q i))
      rw [norm_mul, le_div_iff₀ (by positivity)]
      have hS0 : 0 ≤ ‖S (mQ Q)‖ := norm_nonneg _
      have hf0 : ‖fhat f (mQ Q)‖ ≤ B := norm_fhat_le hB _
      have : ‖fhat f (mQ Q)‖ * ‖S (mQ Q)‖ ≤ B * ‖S (mQ Q)‖ :=
        mul_le_mul_of_nonneg_right hf0 hS0
      nlinarith
  have hTle : ‖T‖ ≤ δ / 2 := by
    rw [hTexp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0]
    have h1 : ‖∑ Q : Quads M, fhat f (mQ Q) * S (mQ Q)‖ ≤
        (Fintype.card (Quads M) : ℝ) * (δ / (2 * P)) := by
      refine (norm_sum_le _ _).trans ((sum_le_sum fun Q _ => hterm Q).trans ?_)
      rw [sum_const, card_univ, nsmul_eq_mul]
    have hmass : C * (Fintype.card (Quads M) : ℝ) ≤ P := kC_mass hM h2
    calc C * ‖∑ Q : Quads M, fhat f (mQ Q) * S (mQ Q)‖
        ≤ C * ((Fintype.card (Quads M) : ℝ) * (δ / (2 * P))) :=
          mul_le_mul_of_nonneg_left h1 hC0
      _ = (C * (Fintype.card (Quads M) : ℝ)) * (δ / (2 * P)) := by ring
      _ ≤ P * (δ / (2 * P)) := mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = δ / 2 := by field_simp
  -- but the smoothed average is large
  have hTge : δ - ∑ i, W i / M i ≤ ‖T‖ := by
    have e : (T : ℂ) = ((∑ j, ω j * f (y j) - ∑ j, ω j * (f (y j) - smooth M f (y j)) : ℝ) : ℂ) := by
      rw [hT]; push_cast
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    have hE : |∑ j, ω j * (f (y j) - smooth M f (y j))| ≤ ∑ i, W i / M i := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |ω j * (f (y j) - smooth M f (y j))| ≤ ∑ j, |ω j| * (∑ i, W i / M i) :=
            sum_le_sum fun j _ => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (abs_sub_smooth hM h2 hW hf (y j)) (abs_nonneg _)
        _ = (∑ j, |ω j|) * (∑ i, W i / M i) := by rw [sum_mul]
        _ ≤ 1 * (∑ i, W i / M i) := mul_le_mul_of_nonneg_right hω hE0
        _ = _ := one_mul _
    have := abs_sub_abs_le_abs_sub (∑ j, ω j * f (y j)) (∑ j, ω j * (f (y j) - smooth M f (y j)))
    linarith
  linarith

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

lemma coe_sum_real {κ : Type*} (s : Finset κ) (f : κ → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : UnitAddCircle) = ∑ i ∈ s, (f i : UnitAddCircle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, AddCircle.coe_add, ih]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The character `x ↦ e(k·x)` of `(ℝ/ℤ)^κ`. -/
def tch (k : κ → ℤ) (x : κ → UnitAddCircle) : ℂ :=
  ((AddCircle.toCircle (∑ i, k i • x i) : Circle) : ℂ)

lemma norm_tch_sub_le (k : κ → ℤ) (t t' : κ → ℝ) :
    ‖tch k (fun i => (t i : UnitAddCircle)) - tch k (fun i => (t' i : UnitAddCircle))‖ ≤
      2 * Real.pi * ∑ i, |(k i : ℝ)| * |t i - t' i| := by
  unfold tch
  have e : ∀ u : κ → ℝ, ∑ i, k i • ((u i : ℝ) : UnitAddCircle) =
      ((∑ i, (k i : ℝ) * u i : ℝ) : UnitAddCircle) := by
    intro u
    rw [coe_sum_real]
    refine sum_congr rfl fun i _ => ?_
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  rw [e t, e t']
  refine (norm_toCircle_sub_le _ _).trans ?_
  gcongr
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_sub, abs_mul]

variable {N : ℕ} [NeZero N]

/-- The grid point `g/N` of `(ℝ/ℤ)^κ`. -/
def gridPt (g : κ → ZMod N) : κ → UnitAddCircle := fun i => ZMod.toAddCircle (g i)

lemma ech_zdot (k : κ → ℤ) (g : κ → ZMod N) : ech (zdot k g) = tch k (gridPt g) := by
  unfold ech zdot tch gridPt
  rw [ZMod.stdAddChar_apply]
  show ((AddCircle.toCircle (ZMod.toAddCircle (∑ i, (k i : ZMod N) * g i)) : Circle) : ℂ) = _
  rw [map_sum]
  congr 3
  funext i
  rw [← zsmul_eq_mul, map_zsmul]

/-- Lipschitz continuity with coordinate weights `w`, tested on arbitrary real lifts. -/
def CLip (w : κ → ℝ) (F : (κ → UnitAddCircle) → ℝ) : Prop :=
  ∀ t t' : κ → ℝ, |F (fun i => (t i : UnitAddCircle)) - F (fun i => (t' i : UnitAddCircle))| ≤
    ∑ i, w i * |t i - t' i|

lemma exists_round (x : UnitAddCircle) :
    ∃ t : ℝ, ∃ z : ZMod N, (t : UnitAddCircle) = x ∧
      ∃ t' : ℝ, (t' : UnitAddCircle) = ZMod.toAddCircle z ∧ |t - t'| ≤ 1 / (2 * N) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨t, ((round (N * t) : ℤ) : ZMod N), rfl,
    (round (N * t) : ℝ) / N, ?_, ?_⟩
  · rw [ZMod.toAddCircle_intCast]
  · have h := abs_sub_round (N * t)
    rw [show t - (round (N * t) : ℝ) / N = (N * t - round (N * t)) / N by field_simp,
      abs_div, abs_of_pos hN, div_le_div_iff₀ hN (by positivity)]
    nlinarith

lemma exists_round_vec (x : κ → UnitAddCircle) :
    ∃ t t' : κ → ℝ, ∃ g : κ → ZMod N, (fun i => (t i : UnitAddCircle)) = x ∧
      (fun i => (t' i : UnitAddCircle)) = gridPt g ∧ ∀ i, |t i - t' i| ≤ 1 / (2 * N) := by
  choose t z ht t' ht' hb using fun i => exists_round (N := N) (x i)
  exact ⟨t, t', z, funext ht, funext ht', hb⟩

lemma gridLip {w : κ → ℝ} {F : (κ → UnitAddCircle) → ℝ} (hF : CLip w F) (y h : κ → ZMod N) :
    |F (gridPt y) - F (gridPt (y - h))| ≤ ∑ i, w i * cn (h i) := by
  have e1 : gridPt y = fun i => ((sc (y i) : ℝ) : UnitAddCircle) := by
    funext i; exact toAddCircle_eq_sc _
  have e2 : gridPt (y - h) = fun i => ((sc (y i) - sc (h i) : ℝ) : UnitAddCircle) := by
    funext i
    simp only [gridPt, Pi.sub_apply, map_sub, toAddCircle_eq_sc, AddCircle.coe_sub]
  rw [e1, e2]
  refine (hF _ _).trans (le_of_eq ?_)
  refine sum_congr rfl fun i _ => ?_
  rw [sub_sub_cancel, cn_eq_abs_sc]

/-- **Weyl lemma on the torus.** -/
theorem weyl_torus {M : κ → ℕ} (hM : ∀ i, 1 ≤ M i) (h2 : ∀ i, 2 * M i ≤ N) {w : κ → ℝ}
    {B δ : ℝ} (hw : ∀ i, 0 ≤ w i) {F : (κ → UnitAddCircle) → ℝ} (hF : CLip w F)
    (hB : ∀ x, |F x| ≤ B) (hmean : ∑ g : κ → ZMod N, F (gridPt g) = 0)
    (hWM : ∑ i, w i / M i < δ / 4) (hN1 : ∑ i, w i / N ≤ δ)
    (hN2 : 2 * B * (∏ i, (2 * M i : ℝ)) * (Real.pi * ∑ i, (2 * M i : ℝ) / N) ≤ δ / 4)
    {ι : Type*} [Fintype ι] (ω : ι → ℝ) (hω : ∑ j, |ω j| ≤ 1) (ξ : ι → κ → UnitAddCircle)
    (hδ : δ ≤ |∑ j, ω j * F (ξ j)|) :
    ∃ k : κ → ℤ, k ≠ 0 ∧ (∀ i, |k i| < 2 * M i) ∧
      δ / 4 ≤ 2 * B * (∏ i, (2 * M i : ℝ)) * ‖∑ j, (ω j : ℂ) * tch k (ξ j)‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  choose t t' y ht ht' hb using fun j => exists_round_vec (N := N) (ξ j)
  -- the grid function
  set f : (κ → ZMod N) → ℝ := fun g => F (gridPt g) with hfdef
  have hfy : ∀ j, |F (ξ j) - f (y j)| ≤ ∑ i, w i / (2 * N) := by
    intro j
    rw [hfdef]; (try dsimp only)
    rw [← ht j, ← ht' j]
    refine (hF _ _).trans (sum_le_sum fun i _ => ?_)
    calc w i * |t j i - t' j i| ≤ w i * (1 / (2 * N)) := mul_le_mul_of_nonneg_left (hb j i) (hw i)
      _ = w i / (2 * N) := by ring
  have hδ' : δ / 2 ≤ |∑ j, ω j * f (y j)| := by
    have hE : |∑ j, ω j * (F (ξ j) - f (y j))| ≤ ∑ i, w i / (2 * N) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |ω j * (F (ξ j) - f (y j))| ≤ ∑ j, |ω j| * ∑ i, w i / (2 * N) :=
            sum_le_sum fun j _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hfy j) (abs_nonneg _)
        _ = (∑ j, |ω j|) * ∑ i, w i / (2 * N) := by rw [sum_mul]
        _ ≤ 1 * ∑ i, w i / (2 * N) :=
            mul_le_mul_of_nonneg_right hω (sum_nonneg fun i _ => by have := hw i; positivity)
        _ = _ := one_mul _
    have e : ∑ i, w i / (2 * N) = (∑ i, w i / N) / 2 := by
      rw [sum_div]; refine sum_congr rfl fun i _ => ?_; field_simp
    have h3 := abs_sub_abs_le_abs_sub (∑ j, ω j * F (ξ j)) (∑ j, ω j * (F (ξ j) - f (y j)))
    have h4 : ∑ j, ω j * F (ξ j) - ∑ j, ω j * (F (ξ j) - f (y j)) = ∑ j, ω j * f (y j) := by
      rw [← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_; ring
    rw [h4] at h3
    linarith
  obtain ⟨k, hk0, hkM, hk⟩ := weyl_grid (N := N) hM h2 hw (fun y h => gridLip hF y h)
    (fun g => hB _) hmean (by linarith) ω hω y hδ'
  refine ⟨k, hk0, hkM, ?_⟩
  -- compare grid characters with characters at the original points
  have hcmp : ‖∑ j, (ω j : ℂ) * ech (zdot k (y j))‖ ≤
      ‖∑ j, (ω j : ℂ) * tch k (ξ j)‖ + Real.pi * ∑ i, (2 * M i : ℝ) / N := by
    have hd : ‖∑ j, (ω j : ℂ) * ech (zdot k (y j)) - ∑ j, (ω j : ℂ) * tch k (ξ j)‖ ≤
        Real.pi * ∑ i, (2 * M i : ℝ) / N := by
      rw [← sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hj : ∀ j, ‖(ω j : ℂ) * ech (zdot k (y j)) - (ω j : ℂ) * tch k (ξ j)‖ ≤
          |ω j| * (Real.pi * ∑ i, (2 * M i : ℝ) / N) := by
        intro j
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [ech_zdot, ← ht' j, ← ht j, norm_sub_rev]
        refine (norm_tch_sub_le k _ _).trans ?_
        rw [mul_sum, mul_sum]
        refine sum_le_sum fun i _ => ?_
        have hki : |(k i : ℝ)| ≤ 2 * M i := by
          have := hkM i
          rw [← Int.cast_abs]
          exact_mod_cast this.le
        have hbi := hb j i
        calc 2 * Real.pi * (|(k i : ℝ)| * |t j i - t' j i|)
            ≤ 2 * Real.pi * ((2 * M i) * (1 / (2 * N))) := by
              gcongr
          _ = Real.pi * ((2 * M i : ℝ) / N) := by field_simp
      calc ∑ j, ‖(ω j : ℂ) * ech (zdot k (y j)) - (ω j : ℂ) * tch k (ξ j)‖
          ≤ ∑ j, |ω j| * (Real.pi * ∑ i, (2 * M i : ℝ) / N) := sum_le_sum fun j _ => hj j
        _ = (∑ j, |ω j|) * (Real.pi * ∑ i, (2 * M i : ℝ) / N) := by rw [sum_mul]
        _ ≤ 1 * (Real.pi * ∑ i, (2 * M i : ℝ) / N) :=
            mul_le_mul_of_nonneg_right hω (by positivity)
        _ = _ := one_mul _
    have := norm_sub_norm_le (∑ j, (ω j : ℂ) * ech (zdot k (y j))) (∑ j, (ω j : ℂ) * tch k (ξ j))
    linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => 0))
  have hP : 0 ≤ 2 * B * (∏ i, (2 * M i : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_left hcmp hP
  nlinarith

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

section File_GT_Vino
/-!
# Geometric sums and Vinogradov's lemma

Used in the proof of Proposition 4.9 (large local quadratic exponential sums).
-/

open Finset

namespace GT

noncomputable section

lemma norm_coe_real_le (s : ℝ) : ‖(s : UnitAddCircle)‖ ≤ |s| := QuotientAddGroup.norm_mk_le_norm

lemma norm_coe_real_eq {s : ℝ} (h : |s| ≤ 1 / 2) : ‖(s : UnitAddCircle)‖ = |s| :=
  (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using h)

end

end GT
end File_GT_Vino

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

variable {p : ℕ} [NeZero p]

end

end GT
end File_GT_MixTV

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

/-! ### Goodness -/

namespace Good

variable {T : Finset (ZMod p)} {A A' : ℝ} {l l' : ZMod p}

lemma mono (h : Good T A l) (hA : A ≤ A') : Good T A' l := fun x =>
  (h x).trans (mul_le_mul_of_nonneg_right hA (snorm_nonneg _))

end Good

/-! ### Box Cauchy–Schwarz -/

section box

variable {α β : Type*} [Fintype α] [Fintype β]

end box

/-! ### Translations of centred regular variables -/

end

end GT
end File_GT_U3Base

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

lemma qd_add (c : Fin 4 → ZMod p) (x2 x3 x4 : ZMod p) :
    qd c x2 x3 x4 0 + qd c x2 x3 x4 1 = qd c x2 x3 x4 2 + qd c x2 x3 x4 3 := by
  simp only [qd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-! ### A general translation estimate inside a context -/

lemma snorm_le_of_regP_ne {Γ : Finset (ZMod p)} {ρ : ℝ} (hρ : 0 ≤ ρ) {x : ZMod p}
    (hx : regP Γ ρ x ≠ 0) : snorm Γ x ≤ ρ :=
  snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ hx) hρ

end

end GT
end File_GT_U3Q

section File_GT_U3Eq
/-!
# Equidistribution of `λ ↦ (λ q₀, λ q₁, λ q₂)` in boxes

Used for the random filters of Green–Tao, Theorem 9.4.  If `(q₀, q₁, q₂)` satisfies no
relation `∑ kᵢ qᵢ = 0` with `0 < max |kᵢ| < 2M`, then for uniformly random `λ ∈ ℤ/pℤ` the
probability that `λ qᵢ + xᵢ` lies in `{cn ≤ ε}` for `i = 0, 1, 2` is close to the product of
the densities.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Counting `{y : cn y ≤ r}` -/

lemma cn_intCast_eq {z : ℤ} (hz : 2 * |(z : ℝ)| ≤ p) : cn (z : ZMod p) = |(z : ℝ)| / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  unfold cn
  rw [ZMod.toAddCircle_intCast, norm_coe_real_eq]
  · rw [abs_div, abs_of_pos hp]
  · rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]; linarith

lemma exists_intCast_of_cn (y : ZMod p) : ∃ z : ℤ, (z : ZMod p) = y ∧ |(z : ℝ)| = p * cn y := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  refine ⟨(y.val : ℤ) - p * round ((y.val : ℝ) / p), ?_, ?_⟩
  · push_cast; simp
  · rw [cn_eq_abs_sc, sc]
    push_cast
    rw [show (y.val : ℝ) - p * (round ((y.val : ℝ) / p) : ℝ) =
      p * ((y.val : ℝ) / p - round ((y.val : ℝ) / p)) by field_simp]
    rw [abs_mul, abs_of_pos hp]

/-- The number of residues `y` with `cn y ≤ r` is `2rp + O(1)`. -/
lemma card_cn_le {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 1 / 2) :
    2 * r * p - 1 ≤ ((univ.filter fun y : ZMod p => cn y ≤ r).card : ℝ) ∧
      ((univ.filter fun y : ZMod p => cn y ≤ r).card : ℝ) ≤ 2 * r * p + 1 := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  set K : ℤ := ⌊r * p⌋ with hK
  have hK0 : 0 ≤ K := Int.floor_nonneg.2 (by positivity)
  have hKle : (K : ℝ) ≤ r * p := Int.floor_le _
  have hKgt : r * p - 1 < (K : ℝ) := by have := Int.sub_one_lt_floor (r * p); linarith
  set I : Finset ℤ := Finset.Icc (-K) K with hI
  have hIcard : (I.card : ℝ) = 2 * K + 1 := by
    rw [hI, Int.card_Icc]
    have : (K + 1 - -K).toNat = (2 * K + 1).toNat := by congr 1; ring
    rw [this]
    have h0 : 0 ≤ 2 * K + 1 := by omega
    rw [show (((2 * K + 1).toNat : ℕ) : ℝ) = (((2 * K + 1).toNat : ℤ) : ℝ) by norm_cast,
      Int.toNat_of_nonneg h0]
    push_cast; ring
  have hmemI : ∀ z : ℤ, z ∈ I ↔ |(z : ℝ)| ≤ K := fun z => by
    rw [hI, Finset.mem_Icc, abs_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast (by omega : -K ≤ z), by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast (show ((-K : ℤ) : ℝ) ≤ z by push_cast; linarith),
        by exact_mod_cast h2⟩
  have himg : univ.filter (fun y : ZMod p => cn y ≤ r) = I.image (fun z : ℤ => (z : ZMod p)) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hy
      obtain ⟨z, rfl, hz⟩ := exists_intCast_of_cn y
      refine ⟨z, (hmemI z).2 ?_, rfl⟩
      have : |(z : ℝ)| ≤ r * p := by rw [hz]; nlinarith
      have hfl : (⌊|(z : ℝ)|⌋ : ℝ) ≤ K := by
        exact_mod_cast Int.floor_mono this
      have : |(z : ℝ)| = ((|z| : ℤ) : ℝ) := by push_cast; rfl
      rw [this] at hfl ⊢
      rwa [Int.floor_intCast] at hfl
    · rintro ⟨z, hz, rfl⟩
      rw [hmemI] at hz
      rw [cn_intCast_eq (by nlinarith), div_le_iff₀ hp]
      linarith
  have hinj : Set.InjOn (fun z : ℤ => (z : ZMod p)) I := by
    intro z hz z' hz' h
    (try simp only at h)
    rw [mem_coe, hmemI] at hz hz'
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    obtain ⟨c, hc⟩ := h
    have hlt : |((z' - z : ℤ) : ℝ)| < p := by
      push_cast
      calc |(z' : ℝ) - z| ≤ |(z' : ℝ)| + |(z : ℝ)| := abs_sub _ _
        _ ≤ 2 * r * p := by linarith
        _ < p := by nlinarith
    rw [hc] at hlt
    push_cast at hlt
    rw [abs_mul, abs_of_pos hp] at hlt
    have hc0 : c = 0 := by
      by_contra hc0
      have : (1 : ℝ) ≤ |(c : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc0
      nlinarith
    rw [hc0, mul_zero, sub_eq_zero] at hc
    exact hc.symm
  rw [himg, card_image_of_injOn hinj, hIcard]
  constructor <;> linarith

/-! ### Trapezoidal cut-offs -/

/-- A trapezoid on `ℝ/ℤ`: `1` on `‖x‖ ≤ a - w`, `0` on `‖x‖ ≥ a`, linear in between. -/
def trap (a w : ℝ) (x : UnitAddCircle) : ℝ := max 0 (min 1 ((a - ‖x‖) / w))

lemma trap_nonneg (a w : ℝ) (x : UnitAddCircle) : 0 ≤ trap a w x := le_max_left _ _

lemma trap_le_one (a w : ℝ) (x : UnitAddCircle) : trap a w x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma trap_eq_zero {a w : ℝ} (hw : 0 < w) {x : UnitAddCircle} (hx : a < ‖x‖) : trap a w x = 0 := by
  unfold trap
  have : (a - ‖x‖) / w < 0 := div_neg_of_neg_of_pos (by linarith) hw
  rw [max_eq_left (le_trans (min_le_right _ _) this.le)]

lemma trap_eq_one {a w : ℝ} (hw : 0 < w) {x : UnitAddCircle} (hx : ‖x‖ ≤ a - w) :
    trap a w x = 1 := by
  unfold trap
  have : 1 ≤ (a - ‖x‖) / w := by rw [le_div_iff₀ hw]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma trap_lip {a w : ℝ} (hw : 0 < w) (t t' : ℝ) :
    |trap a w (t : UnitAddCircle) - trap a w (t' : UnitAddCircle)| ≤ 1 / w * |t - t'| := by
  have hclamp : ∀ u v : ℝ, |max 0 (min 1 u) - max 0 (min 1 v)| ≤ |u - v| := by
    intro u v
    rcases le_total u v with h | h
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (max_le_max le_rfl (min_le_min le_rfl h))),
        abs_sub_comm, abs_of_nonneg (by linarith)]
      rcases le_total v 1 with h1 | h1 <;> rcases le_total u 0 with h2 | h2 <;>
        rcases le_total u 1 with h3 | h3 <;> rcases le_total v 0 with h4 | h4 <;>
        simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, *] <;> linarith
    · rw [abs_of_nonneg (sub_nonneg.2 (max_le_max le_rfl (min_le_min le_rfl h))),
        abs_of_nonneg (by linarith)]
      rcases le_total u 1 with h1 | h1 <;> rcases le_total v 0 with h2 | h2 <;>
        rcases le_total v 1 with h3 | h3 <;> rcases le_total u 0 with h4 | h4 <;>
        simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, *] <;> linarith
  refine (hclamp _ _).trans ?_
  have hn : |‖(t : UnitAddCircle)‖ - ‖(t' : UnitAddCircle)‖| ≤ |t - t'| := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← AddCircle.coe_sub]; exact norm_coe_real_le _
  rw [← sub_div, abs_div, abs_of_pos hw, div_le_iff₀ hw]
  calc |a - ‖(t : UnitAddCircle)‖ - (a - ‖(t' : UnitAddCircle)‖)|
      = |‖(t : UnitAddCircle)‖ - ‖(t' : UnitAddCircle)‖| := by
        rw [abs_sub_comm]; congr 1; ring
    _ ≤ |t - t'| := hn
    _ = 1 / w * |t - t'| * w := by field_simp

/-- The product cut-off on `(ℝ/ℤ)³`. -/
def psi3 (a w : ℝ) (x : Fin 3 → UnitAddCircle) : ℝ :=
  trap a w (x 0) * trap a w (x 1) * trap a w (x 2)

lemma psi3_nonneg (a w : ℝ) (x : Fin 3 → UnitAddCircle) : 0 ≤ psi3 a w x := by
  unfold psi3
  exact mul_nonneg (mul_nonneg (trap_nonneg _ _ _) (trap_nonneg _ _ _)) (trap_nonneg _ _ _)

lemma psi3_le_one (a w : ℝ) (x : Fin 3 → UnitAddCircle) : psi3 a w x ≤ 1 := by
  unfold psi3
  have h0 := trap_nonneg a w; have h1 := trap_le_one a w
  calc trap a w (x 0) * trap a w (x 1) * trap a w (x 2) ≤ 1 * 1 * 1 := by
        gcongr <;> first | exact h0 _ | exact h1 _ | exact mul_nonneg (h0 _) (h0 _)
    _ = 1 := by norm_num

lemma abs_mul3_sub_le {a b c a' b' c' : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb' : 0 ≤ b') (hb1 : b' ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ha' : 0 ≤ a') (ha1' : a' ≤ 1) (hb : 0 ≤ b) (hb1' : b ≤ 1)
    (hc' : 0 ≤ c') (hc1' : c' ≤ 1) :
    |a * b * c - a' * b' * c'| ≤ |a - a'| + |b - b'| + |c - c'| := by
  have e : a * b * c - a' * b' * c' = (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]
    calc |a - a'| * b * c ≤ |a - a'| * 1 * 1 := by gcongr
      _ = _ := by ring
  · rw [abs_mul, abs_mul, abs_of_nonneg ha', abs_of_nonneg hc]
    calc a' * |b - b'| * c ≤ 1 * |b - b'| * 1 := by gcongr
      _ = _ := by ring
  · rw [abs_mul, abs_mul, abs_of_nonneg ha', abs_of_nonneg hb']
    calc a' * b' * |c - c'| ≤ 1 * 1 * |c - c'| := by gcongr
      _ = _ := by ring

lemma psi3_clip {a w : ℝ} (hw : 0 < w) : CLip (fun _ => 1 / w) (psi3 a w) := by
  intro t t'
  unfold psi3
  have h0 := trap_nonneg a w; have h1 := trap_le_one a w
  refine (abs_mul3_sub_le (h0 _) (h1 _) (h0 _) (h1 _) (h0 _) (h1 _) (h0 _) (h1 _) (h0 _) (h1 _)
    (h0 _) (h1 _)).trans ?_
  simp only [Fin.sum_univ_three]
  have := trap_lip (a := a) hw (t 0) (t' 0)
  have := trap_lip (a := a) hw (t 1) (t' 1)
  have := trap_lip (a := a) hw (t 2) (t' 2)
  linarith

/-! ### The equidistribution estimate -/

/-- Equidistribution of `λ ↦ (λ qᵢ + xᵢ)ᵢ` for Lipschitz test functions, for generic `q`. -/
theorem equi3 (hp : p.Prime) {M : ℕ} (hM : 1 ≤ M) (h2M : 2 * M ≤ p) {W δ : ℝ} (hW : 0 ≤ W)
    (hδ : 0 < δ) {ψ : (Fin 3 → UnitAddCircle) → ℝ} (hψ : CLip (fun _ => W) ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hWM : 3 * (W / M) < δ / 4) (hN1 : 3 * (W / p) ≤ δ)
    (hN2 : 2 * (2 * M : ℝ) ^ 3 * (Real.pi * (3 * ((2 * M : ℝ) / p))) ≤ δ / 4)
    (q x : Fin 3 → ZMod p)
    (hgen : ∀ k : Fin 3 → ℤ, k ≠ 0 → (∀ i, |k i| < 2 * M) → zdot k q ≠ 0) :
    |∑ l : ZMod p, (1 / p : ℝ) * ψ (gridPt (fun i => l * q i + x i)) -
      (1 / p ^ 3 : ℝ) * ∑ y : Fin 3 → ZMod p, ψ (gridPt y)| < δ := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  set m : ℝ := (1 / p ^ 3 : ℝ) * ∑ y : Fin 3 → ZMod p, ψ (gridPt y) with hm
  have hcard : (Fintype.card (Fin 3 → ZMod p) : ℝ) = p ^ 3 := by
    simp [Fintype.card_fun, ZMod.card]
  have hm0 : 0 ≤ m := by rw [hm]; exact mul_nonneg (by positivity) (sum_nonneg fun y _ => hψ0 _)
  have hm1 : m ≤ 1 := by
    rw [hm]
    have : ∑ y : Fin 3 → ZMod p, ψ (gridPt y) ≤ ∑ _y : Fin 3 → ZMod p, (1 : ℝ) :=
      sum_le_sum fun y _ => hψ1 _
    rw [sum_const, card_univ, nsmul_eq_mul, hcard, mul_one] at this
    calc 1 / p ^ 3 * ∑ y : Fin 3 → ZMod p, ψ (gridPt y) ≤ 1 / p ^ 3 * p ^ 3 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 := by field_simp
  by_contra hcon
  push_neg at hcon
  set F : (Fin 3 → UnitAddCircle) → ℝ := fun z => ψ z - m with hF
  have hFl : CLip (fun _ => W) F := by
    intro t t'
    have := hψ t t'
    simp only [hF]
    rwa [sub_sub_sub_cancel_right]
  have hFB : ∀ z, |F z| ≤ 1 := fun z => by
    simp only [hF]; rw [abs_le]; constructor <;> linarith [hψ0 z, hψ1 z]
  have hFmean : ∑ g : Fin 3 → ZMod p, F (gridPt g) = 0 := by
    simp only [hF, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hcard, hm]
    field_simp
    ring
  have hω : ∑ _l : ZMod p, |(1 / p : ℝ)| ≤ 1 := by
    rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, abs_of_pos (by positivity)]
    field_simp; rfl
  have hδ' : δ ≤ |∑ l : ZMod p, (1 / p : ℝ) * F (gridPt (fun i => l * q i + x i))| := by
    have e : ∑ l : ZMod p, (1 / p : ℝ) * F (gridPt (fun i => l * q i + x i)) =
        ∑ l : ZMod p, (1 / p : ℝ) * ψ (gridPt (fun i => l * q i + x i)) - m := by
      simp only [hF, mul_sub, sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      congr 1
      field_simp
    rw [e]; exact hcon
  obtain ⟨k, hk0, hkM, hk⟩ := weyl_torus (κ := Fin 3) (N := p) (M := fun _ => M)
    (fun _ => hM) (fun _ => h2M) (w := fun _ => W) (B := 1) (δ := δ) (fun _ => hW) hFl hFB
    hFmean (by simp only [Fin.sum_univ_three]; linarith)
    (by simp only [Fin.sum_univ_three]; linarith)
    (by
      simp only [Fin.sum_univ_three, Fin.prod_univ_three]
      have : 2 * 1 * ((2 * M : ℝ) * (2 * M) * (2 * M)) * (Real.pi *
          ((2 * M : ℝ) / p + (2 * M) / p + (2 * M) / p)) =
          2 * (2 * M : ℝ) ^ 3 * (Real.pi * (3 * ((2 * M : ℝ) / p))) := by ring
      push_cast
      linarith)
    (fun _ : ZMod p => (1 / p : ℝ)) hω (fun l => gridPt (fun i => l * q i + x i)) hδ'
  have hz : ∑ l : ZMod p, ((1 / p : ℝ) : ℂ) * tch k (gridPt (fun i => l * q i + x i)) = 0 := by
    have e : ∀ l : ZMod p, tch k (gridPt (fun i => l * q i + x i)) =
        ech (zdot k x) * ech (l * zdot k q) := fun l => by
      rw [← ech_zdot, ← ech_add]
      congr 1
      simp only [zdot, mul_add, sum_add_distrib, mul_sum]
      rw [add_comm]; congr 1
      exact sum_congr rfl fun i _ => by ring
    simp_rw [e, ← mul_sum, ← mul_assoc]
    have := sum_ech_mul (N := p) (zdot k q)
    rw [this, if_neg (hgen k hk0 hkM), mul_zero]
  rw [hz, norm_zero, mul_zero] at hk
  linarith

/-! ### Box probabilities -/

/-- Probability over uniform `λ` that `λ qᵢ + xᵢ ∈ {cn ≤ r}` for `i = 0, 1, 2`. -/
def boxP (r : ℝ) (q x : Fin 3 → ZMod p) : ℝ :=
  ∑ l : ZMod p, (1 / p : ℝ) * (if ∀ i, cn (l * q i + x i) ≤ r then 1 else 0)

/-- Density of `{cn ≤ r}`. -/
def dens (p : ℕ) [NeZero p] (r : ℝ) : ℝ :=
  (1 / p : ℝ) * ((univ.filter fun y : ZMod p => cn y ≤ r).card : ℝ)

lemma mean_prod3 (g : ZMod p → ℝ) :
    (1 / p ^ 3 : ℝ) * ∑ y : Fin 3 → ZMod p, (g (y 0) * g (y 1) * g (y 2)) =
      ((1 / p : ℝ) * ∑ z, g z) ^ 3 := by
  have e : ∑ y : Fin 3 → ZMod p, (g (y 0) * g (y 1) * g (y 2)) = ∏ _i : Fin 3, ∑ z, g z := by
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Fin.prod_univ_three]
  rw [e, prod_const, card_univ, Fintype.card_fin]
  ring

lemma dens_eq (r : ℝ) : dens p r = (1 / p : ℝ) * ∑ z : ZMod p, (if cn z ≤ r then 1 else 0) := by
  unfold dens
  rw [sum_boole]

lemma gridPt_apply (y : Fin 3 → ZMod p) (i : Fin 3) : ‖gridPt y i‖ = cn (y i) := rfl

/-- Two-sided box estimate for generic `q`. -/
theorem boxP_bounds (hp : p.Prime) {M : ℕ} (hM : 1 ≤ M) (h2M : 2 * M ≤ p) {r w δ : ℝ}
    (hw : 0 < w) (hδ : 0 < δ)
    (hWM : 3 * (1 / w / M) < δ / 4) (hN1 : 3 * (1 / w / p) ≤ δ)
    (hN2 : 2 * (2 * M : ℝ) ^ 3 * (Real.pi * (3 * ((2 * M : ℝ) / p))) ≤ δ / 4)
    (q x : Fin 3 → ZMod p)
    (hgen : ∀ k : Fin 3 → ℤ, k ≠ 0 → (∀ i, |k i| < 2 * M) → zdot k q ≠ 0) :
    dens p (r - w) ^ 3 - δ ≤ boxP r q x ∧ boxP r q x ≤ dens p (r + w) ^ 3 + δ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hW : (0 : ℝ) ≤ 1 / w := by positivity
  constructor
  · have hE := equi3 hp hM h2M hW hδ (psi3_clip (a := r) hw) (psi3_nonneg r w) (psi3_le_one r w)
      hWM hN1 hN2 q x hgen
    have h1 : ∑ l : ZMod p, (1 / p : ℝ) * psi3 r w (gridPt (fun i => l * q i + x i)) ≤ boxP r q x := by
      unfold boxP
      refine sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
      split_ifs with h
      · exact psi3_le_one _ _ _
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        unfold psi3
        have hz : trap r w (gridPt (fun i => l * q i + x i) i) = 0 := trap_eq_zero hw hi
        fin_cases i <;> simp_all
    have h2 : dens p (r - w) ^ 3 ≤ (1 / p ^ 3 : ℝ) * ∑ y : Fin 3 → ZMod p, psi3 r w (gridPt y) := by
      rw [dens_eq, ← mean_prod3]
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => ?_) (by positivity)
      unfold psi3
      have hle : ∀ i, (if cn (y i) ≤ r - w then (1 : ℝ) else 0) ≤ trap r w (gridPt y i) := by
        intro i
        split_ifs with h
        · rw [trap_eq_one hw (by rw [gridPt_apply]; exact h)]
        · exact trap_nonneg _ _ _
      have h0 : ∀ i, (0 : ℝ) ≤ if cn (y i) ≤ r - w then (1 : ℝ) else 0 := fun i => by
        split_ifs <;> norm_num
      exact mul_le_mul (mul_le_mul (hle 0) (hle 1) (h0 1) (trap_nonneg _ _ _)) (hle 2) (h0 2)
        (mul_nonneg (trap_nonneg _ _ _) (trap_nonneg _ _ _))
    have := (abs_lt.1 hE).1
    linarith
  · have hE := equi3 hp hM h2M hW hδ (psi3_clip (a := r + w) hw) (psi3_nonneg (r + w) w)
      (psi3_le_one (r + w) w) hWM hN1 hN2 q x hgen
    have h1 : boxP r q x ≤ ∑ l : ZMod p, (1 / p : ℝ) * psi3 (r + w) w (gridPt (fun i => l * q i + x i)) := by
      unfold boxP
      refine sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
      split_ifs with h
      · unfold psi3
        have : ∀ i, trap (r + w) w (gridPt (fun i => l * q i + x i) i) = 1 := fun i =>
          trap_eq_one hw (by rw [gridPt_apply]; linarith [h i])
        rw [this 0, this 1, this 2]; norm_num
      · exact psi3_nonneg _ _ _
    have h2 : (1 / p ^ 3 : ℝ) * ∑ y : Fin 3 → ZMod p, psi3 (r + w) w (gridPt y) ≤ dens p (r + w) ^ 3 := by
      rw [dens_eq, ← mean_prod3]
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => ?_) (by positivity)
      unfold psi3
      have hle : ∀ i, trap (r + w) w (gridPt y i) ≤ (if cn (y i) ≤ r + w then (1 : ℝ) else 0) := by
        intro i
        split_ifs with h
        · exact trap_le_one _ _ _
        · push_neg at h
          rw [trap_eq_zero hw (by rw [gridPt_apply]; exact h)]
      have h0 : ∀ i, (0 : ℝ) ≤ trap (r + w) w (gridPt y i) := fun i => trap_nonneg _ _ _
      exact mul_le_mul (mul_le_mul (hle 0) (hle 1) (h0 1) (by split_ifs <;> norm_num)) (hle 2) (h0 2)
        (mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num))
    have := (abs_lt.1 hE).2
    linarith

lemma dens_bounds {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 1 / 2) :
    2 * r - 1 / p ≤ dens p r ∧ dens p r ≤ 2 * r + 1 / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨h1, h2⟩ := card_cn_le (p := p) hr hr2
  unfold dens
  constructor
  · rw [show 2 * r - 1 / p = 1 / p * (2 * r * p - 1) by field_simp]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [show 2 * r + 1 / p = 1 / p * (2 * r * p + 1) by field_simp]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

lemma box_arith_lo {x0 d b δ : ℝ} (hx00 : 0 < x0) (hx01 : x0 ≤ 1 / 40)
    (hlow : 1 / 100 * (1 - x0) ≤ d) (hlo : d ^ 3 - δ ≤ b) (hδx : δ = 1 / 10 ^ 6 * (4 * x0)) :
    1 / 10 ^ 6 * (1 - 10 * x0) ≤ b := by
  have hd0 : 0 ≤ (1 / 100 : ℝ) * (1 - x0) := mul_nonneg (by norm_num) (by linarith)
  have h3 := pow_le_pow_left₀ hd0 hlow 3
  have e1 : ((1 / 100 : ℝ) * (1 - x0)) ^ 3 = (1 / 10 ^ 6) * (1 - x0) ^ 3 := by ring
  rw [e1] at h3
  have k : 0 ≤ x0 ^ 2 * (3 - x0) := mul_nonneg (sq_nonneg _) (by linarith)
  have : (1 - x0) ^ 3 = 1 - 3 * x0 + x0 ^ 2 * (3 - x0) := by ring
  subst hδx
  nlinarith

lemma box_arith_hi {x0 d b δ : ℝ} (hx00 : 0 < x0) (hx01 : x0 ≤ 1 / 40) (hd0 : 0 ≤ d)
    (hup : d ≤ 1 / 100 * (1 + x0)) (hhi : b ≤ d ^ 3 + δ) (hδx : δ = 1 / 10 ^ 6 * (4 * x0)) :
    b ≤ 1 / 10 ^ 6 * (1 + 10 * x0) := by
  have h3 := pow_le_pow_left₀ hd0 hup 3
  have e1 : ((1 / 100 : ℝ) * (1 + x0)) ^ 3 = (1 / 10 ^ 6) * (1 + x0) ^ 3 := by ring
  rw [e1] at h3
  have hx2 : x0 ^ 2 ≤ x0 / 40 := by
    have := mul_le_mul_of_nonneg_left hx01 hx00.le
    nlinarith
  have k : 0 ≤ x0 * (1 - 3 * x0 - x0 ^ 2) := mul_nonneg hx00.le (by linarith)
  have : (1 + x0) ^ 3 = 1 + 4 * x0 - x0 * (1 - 3 * x0 - x0 ^ 2) := by ring
  subst hδx
  nlinarith

/-- Uniform box estimate with explicit parameters: for generic `q`, the probability that
`λ qᵢ + xᵢ ∈ {cn ≤ 1/200}` for all `i` is `10⁻⁶ (1 + O(1/m))`. -/
theorem boxP_unif (hp : p.Prime) {m : ℕ} (hm : 1 ≤ m) (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p)
    (q x : Fin 3 → ZMod p)
    (hgen : ∀ k : Fin 3 → ℤ, k ≠ 0 → (∀ i, |k i| < 2 * gM m) → zdot k q ≠ 0) :
    (1 / 10 ^ 6 : ℝ) * (1 - 1 / (4 * m)) ≤ boxP (1 / 200) q x ∧
      boxP (1 / 200) q x ≤ (1 / 10 ^ 6 : ℝ) * (1 + 1 / (4 * m)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hm10 : (m : ℝ) ≤ (m : ℝ) ^ 10 := le_self_pow₀ hm1 (by norm_num)
  have hm9 : (m : ℝ) ^ 9 ≤ (m : ℝ) ^ 10 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm2 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 10 := pow_le_pow_right₀ hm1 (by norm_num)
  have hgM : (gM m : ℝ) = 2 * 10 ^ 12 * m ^ 2 := by unfold gM; push_cast; ring
  have hgM1 : 1 ≤ gM m := by unfold gM; have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm; omega
  have hpm' : (2 * gM m : ℝ) ≤ p := by rw [hgM]; nlinarith
  have h2M : 2 * gM m ≤ p := by exact_mod_cast hpm'
  set w : ℝ := 1 / (16000 * m) with hw
  set δ : ℝ := 1 / (10 ^ 7 * m) with hδ
  have hw0 : 0 < w := by positivity
  have hδ0 : 0 < δ := by positivity
  have hWM : 3 * (1 / w / (gM m : ℝ)) < δ / 4 := by
    have e1 : 3 * (1 / w / (gM m : ℝ)) = 24 / (10 ^ 9 * m) := by
      rw [hgM, hw]; field_simp; ring
    have e2 : δ / 4 = 25 / (10 ^ 9 * m) := by rw [hδ]; field_simp; ring
    rw [e1, e2]; exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  have hN1 : 3 * (1 / w / p) ≤ δ := by
    have e1 : 3 * (1 / w / p) = 48000 * m / p := by rw [hw]; field_simp; ring
    rw [e1, hδ, div_le_div_iff₀ hp0 (by positivity)]
    nlinarith
  have hN2 : 2 * (2 * (gM m : ℕ) : ℝ) ^ 3 * (Real.pi * (3 * ((2 * (gM m : ℕ) : ℝ) / p))) ≤ δ / 4 := by
    have e1 : 2 * (2 * (gM m : ℕ) : ℝ) ^ 3 * (Real.pi * (3 * ((2 * (gM m : ℕ) : ℝ) / p))) =
        (2 * 64 * 10 ^ 36 * 12 * 10 ^ 12) * Real.pi * (m : ℝ) ^ 8 / p := by
      rw [hgM]; ring
    have e2 : δ / 4 = 1 / (4 * 10 ^ 7 * m) := by rw [hδ]; field_simp
    rw [e1, e2, div_le_div_iff₀ hp0 (by positivity)]
    have hm8 : (m : ℝ) ^ 8 * m ≤ (m : ℝ) ^ 10 := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hm1 (by norm_num)
    have hpi := Real.pi_le_four
    have hm8p : 0 ≤ (m : ℝ) ^ 8 := by positivity
    calc (2 * 64 * 10 ^ 36 * 12 * 10 ^ 12) * Real.pi * (m : ℝ) ^ 8 * (4 * 10 ^ 7 * m)
        ≤ (2 * 64 * 10 ^ 36 * 12 * 10 ^ 12) * 4 * (m : ℝ) ^ 8 * (4 * 10 ^ 7 * m) := by
          gcongr
      _ = (2 * 64 * 10 ^ 36 * 12 * 10 ^ 12 * 4 * 4 * 10 ^ 7) * ((m : ℝ) ^ 8 * m) := by ring
      _ ≤ 10 ^ 60 * (m : ℝ) ^ 10 := by nlinarith
      _ ≤ 1 * p := by linarith
  obtain ⟨hlo, -⟩ := boxP_bounds hp hgM1 h2M (r := 1 / 200) hw0 hδ0 hWM hN1 hN2 q x hgen
  obtain ⟨-, hhi⟩ := boxP_bounds hp hgM1 h2M (r := 1 / 200) hw0 hδ0 hWM hN1 hN2 q x hgen
  have hw1 : w ≤ 1 / 16000 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hpinv : 1 / (p : ℝ) ≤ 1 / (8000 * m) := by
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  obtain ⟨d1, -⟩ := dens_bounds (p := p) (r := 1 / 200 - w) (by linarith) (by linarith)
  obtain ⟨-, d2⟩ := dens_bounds (p := p) (r := 1 / 200 + w) (by linarith) (by linarith)
  set x0 : ℝ := 1 / (40 * m) with hx0
  have hx00 : 0 < x0 := by positivity
  have hx01 : x0 ≤ 1 / 40 := by rw [hx0]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hwx : 2 * w + 1 / p ≤ x0 / 100 := by
    have : 2 * w = x0 / 200 := by rw [hw, hx0]; field_simp; ring
    have : 1 / (8000 * (m : ℝ)) = x0 / 200 := by rw [hx0]; field_simp; ring
    linarith
  have hlow : (1 / 100 : ℝ) * (1 - x0) ≤ dens p (1 / 200 - w) := by linarith
  have hup : dens p (1 / 200 + w) ≤ (1 / 100 : ℝ) * (1 + x0) := by linarith
  have hδx : δ = (1 / 10 ^ 6) * (4 * x0) := by rw [hδ, hx0]; field_simp; ring
  have h4 : 1 / (4 * (m : ℝ)) = 10 * x0 := by rw [hx0]; field_simp; ring
  rw [h4]
  have hd0 : 0 ≤ dens p (1 / 200 + w) := by unfold dens; positivity
  clear_value w δ x0
  exact ⟨box_arith_lo hx00 hx01 hlow hlo hδx, box_arith_hi hx00 hx01 hd0 hup hhi hδx⟩

end

end GT
end File_GT_U3Eq

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

lemma cn_two_mul {z : ZMod p} (hz : cn z ≤ 1 / 4) : cn (2 * z) = 2 * cn z := by
  have e : ZMod.toAddCircle (2 * z) = ((2 * sc z : ℝ) : UnitAddCircle) := by
    rw [show (2 : ZMod p) * z = z + z by ring, map_add, toAddCircle_eq_sc, ← AddCircle.coe_add]
    congr 1; ring
  have hs : |sc z| ≤ 1 / 4 := by rw [← cn_eq_abs_sc]; exact hz
  calc cn (2 * z) = ‖((2 * sc z : ℝ) : UnitAddCircle)‖ := by unfold cn; rw [e]
    _ = |2 * sc z| := norm_coe_real_eq (by rw [abs_mul, abs_two]; linarith)
    _ = 2 * cn z := by rw [abs_mul, abs_two, cn_eq_abs_sc]

lemma snorm_two_mul (S : Finset (ZMod p)) (h : ZMod p) : snorm S (2 * h) ≤ 2 * snorm S h := by
  rw [show (2 : ZMod p) * h = h + h by ring]
  exact (snorm_add_le _ _).trans (le_of_eq (by ring))

lemma exists_double {S : Finset (ZMod p)} {σ : ZMod p} {ρv : ℝ} :
    ∀ n : ℕ, ∀ h : ZMod p, 1 / 2 ^ (n + 2) < cn (σ * h) → snorm S h < cn (σ * h) * ρv →
      ∃ h', 1 / 4 < cn (σ * h') ∧ snorm S h' < cn (σ * h') * ρv := by
  intro n
  induction n with
  | zero =>
    intro h h1 h2
    have : (1 : ℝ) / 2 ^ (0 + 2) = 1 / 4 := by norm_num
    exact ⟨h, by linarith, h2⟩
  | succ n ih =>
    intro h h1 h2
    by_cases hq : 1 / 4 < cn (σ * h)
    · exact ⟨h, hq, h2⟩
    · push_neg at hq
      have e : cn (σ * (2 * h)) = 2 * cn (σ * h) := by
        rw [show σ * (2 * h) = 2 * (σ * h) by ring]; exact cn_two_mul hq
      refine ih (2 * h) ?_ ?_
      · rw [e]
        have : (1 : ℝ) / 2 ^ (n + 1 + 2) = 1 / 2 ^ (n + 2) / 2 := by
          rw [show n + 1 + 2 = (n + 2) + 1 by ring, pow_succ]; field_simp
        rw [this] at h1; linarith
      · rw [e]
        have := snorm_two_mul S h
        have hρv : 0 < ρv := by
          by_contra hn; push_neg at hn
          have := snorm_nonneg (S := S) h
          nlinarith [cn_nonneg (σ * h)]
        nlinarith

/-- A very bad `σ` admits a shift `h'` with `cn (σ h') > 1/4` and `‖h'‖_{S^⊥} ≤ ρv/2`. -/
lemma exists_shift_of_not_good {S : Finset (ZMod p)} {σ : ZMod p} {ρv : ℝ} (hρv : 0 < ρv)
    (hb : ¬ Good S (1 / ρv) σ) : ∃ h', 1 / 4 < cn (σ * h') ∧ snorm S h' ≤ ρv / 2 := by
  unfold Good at hb
  push_neg at hb
  obtain ⟨h, hh⟩ := hb
  have hs0 := snorm_nonneg (S := S) h
  have h2 : snorm S h < cn (σ * h) * ρv := by
    rw [one_div, inv_mul_eq_div, div_lt_iff₀ hρv] at hh; linarith
  have hpos : 0 < cn (σ * h) := by
    by_contra hc; push_neg at hc
    have : cn (σ * h) * ρv ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hρv.le
    linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
  have hn' : 1 / 2 ^ (n + 2) < cn (σ * h) := by
    have : (1 : ℝ) / 2 ^ (n + 2) ≤ (1 / 2) ^ n := by
      rw [one_div_pow, pow_add]
      exact one_div_le_one_div_of_le (by positivity) (by
        have : (1 : ℝ) ≤ 2 ^ 2 := by norm_num
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n])
    linarith
  obtain ⟨h', h1, h2'⟩ := exists_double n h hn' h2
  refine ⟨h', h1, ?_⟩
  have := cn_le_half (σ * h')
  nlinarith

/-- For very bad `σ`, `cn (σ h) ≤ 1/8` has probability at most about `1/2`. -/
lemma prob_small_le_half {S : Finset (ZMod p)} {σ : ZMod p} {ρh ρv : ℝ} (hρh : 0 < ρh)
    (hρv : 0 < ρv) (h4 : 2 * ρv ≤ ρh) (hb : ¬ Good S (1 / ρv) σ) :
    ∑ h, regP S ρh h * (if cn (σ * h) ≤ 1 / 8 then 1 else 0) ≤
      1 / 2 + 50 * S.card * (ρv / 2) / ρh / 2 := by
  classical
  obtain ⟨h', h1, h2⟩ := exists_shift_of_not_good hρv hb
  have hP := regP_isDist S hρh.le
  set g : ZMod p → ℝ := fun h => if cn (σ * h) ≤ 1 / 8 then 1 else 0 with hg
  have hsh := regP_shift_real (Γ := S) subset_rfl hρh (by positivity : 0 ≤ ρv / 2) (by linarith)
    ((mem_bohr_iff_snorm (by positivity)).2 h2) g (B := 1) (fun x => by
      simp only [hg]; split_ifs <;> norm_num)
  have hdis : ∀ h, g h + g (h + h') ≤ 1 := by
    intro h
    simp only [hg]
    split_ifs with ha hb'
    · exfalso
      have : cn (σ * h') ≤ 1 / 4 := by
        have e : σ * h' = σ * (h + h') - σ * h := by ring
        rw [e]; have := cn_sub_le (σ * (h + h')) (σ * h); linarith
      linarith
    all_goals norm_num
  have hsum : ∑ h, regP S ρh h * g h + ∑ h, regP S ρh h * g (h + h') ≤ 1 := by
    rw [← sum_add_distrib]
    calc ∑ h, (regP S ρh h * g h + regP S ρh h * g (h + h')) ≤ ∑ h, regP S ρh h * 1 :=
          sum_le_sum fun h _ => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hdis h) (hP.1 h)
      _ = 1 := by rw [← sum_mul, hP.2, one_mul]
  have := (abs_le.1 hsh).1
  linarith

/-! ### One filter -/

/-- Thresholds of the filters: `1/200` for the first three components, `1/10` for the last. -/
def fthr (i : Fin 4) : ℝ := if i = 3 then 1 / 10 else 1 / 200

/-- The filter with parameters `(h, l)` keeps `q`. -/
def fev (ξ : ZMod p → ZMod p) (h l : ZMod p) (q : Fin 4 → ZMod p) : Prop :=
  ∀ i, cn (l * q i + ξ (q i) * h) ≤ fthr i

open Classical in
/-- The probability that a random filter keeps `q`. -/
def fprob (S : Finset (ZMod p)) (ρh : ℝ) (ξ : ZMod p → ZMod p) (q : Fin 4 → ZMod p) : ℝ :=
  ∑ h, regP S ρh h * ∑ l, (1 / p : ℝ) * (if fev ξ h l q then 1 else 0)

/-- `(q₀, q₁, q₂)` satisfies no small linear relation. -/
def gen3 (M : ℕ) (q : Fin 4 → ZMod p) : Prop :=
  ∀ k : Fin 3 → ℤ, k ≠ 0 → (∀ i, |k i| < 2 * M) → zdot k ![q 0, q 1, q 2] ≠ 0

lemma le_wavg' {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (F : α → ℝ) {c : ℝ} (h : ∀ x, P x ≠ 0 → c ≤ F x) : c ≤ ∑ x, P x * F x := by
  have := wavg_le hP hP1 (fun x => -F x) (B := -c) (fun x hx => by linarith [h x hx])
  simp only [mul_neg, sum_neg_distrib] at this
  linarith

lemma fev_identity (ξ : ZMod p → ZMod p) (h l : ZMod p) {q : Fin 4 → ZMod p}
    (hq : q 0 + q 1 = q 2 + q 3) :
    l * q 3 + ξ (q 3) * h = (l * q 0 + ξ (q 0) * h) + (l * q 1 + ξ (q 1) * h) -
      (l * q 2 + ξ (q 2) * h) - sig ξ q * h := by
  have : q 3 = q 0 + q 1 - q 2 := by rw [hq]; ring
  unfold sig
  rw [this]
  simp only [← this]
  rw [this]; ring

lemma boxP_eq_three (ξ : ZMod p → ZMod p) (h : ZMod p) (q : Fin 4 → ZMod p) :
    boxP (1 / 200) ![q 0, q 1, q 2] (fun i => ξ (![q 0, q 1, q 2] i) * h) =
      ∑ l, (1 / p : ℝ) * (if cn (l * q 0 + ξ (q 0) * h) ≤ 1 / 200 ∧
        cn (l * q 1 + ξ (q 1) * h) ≤ 1 / 200 ∧ cn (l * q 2 + ξ (q 2) * h) ≤ 1 / 200 then 1 else 0) := by
  unfold boxP
  refine sum_congr rfl fun l _ => ?_
  congr 2
  apply propext
  constructor
  · intro H; exact ⟨H 0, H 1, H 2⟩
  · rintro ⟨a, b, c⟩ i; fin_cases i
    · exact a
    · exact b
    · exact c

/-- A quadruple respected by `ξ` survives a filter with probability `≈ 10⁻⁶`. -/
theorem fprob_good (hp : p.Prime) {S : Finset (ZMod p)} {ρh A : ℝ} (hρh : 0 < ρh)
    (hA : A * ρh ≤ 1 / 1000) (hA0 : 0 ≤ A) {m : ℕ} (hm : 1 ≤ m)
    (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p) (ξ : ZMod p → ZMod p) {q : Fin 4 → ZMod p}
    (hq : q 0 + q 1 = q 2 + q 3) (hg : Good S A (sig ξ q)) (hgen : gen3 (gM m) q) :
    (1 / 10 ^ 6 : ℝ) * (1 - 1 / (4 * m)) ≤ fprob S ρh ξ q := by
  classical
  have hP := regP_isDist S hρh.le
  refine le_wavg' hP.1 hP.2 _ fun h hh => ?_
  have hsn : snorm S h ≤ ρh := snorm_le_of_regP_ne hρh.le hh
  have hσ : cn (sig ξ q * h) ≤ 1 / 1000 := by
    refine (hg h).trans ?_
    calc A * snorm S h ≤ A * ρh := mul_le_mul_of_nonneg_left hsn hA0
      _ ≤ 1 / 1000 := hA
  have hb := (boxP_unif hp hm hpm ![q 0, q 1, q 2] (fun i => ξ (![q 0, q 1, q 2] i) * h) hgen).1
  rw [boxP_eq_three] at hb
  refine hb.trans (sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (by positivity))
  split_ifs with h3 h4 <;> try norm_num
  exfalso; apply h4
  obtain ⟨a, b, c⟩ := h3
  intro i
  fin_cases i
  · simpa [fthr] using a
  · simpa [fthr] using b
  · simpa [fthr] using c
  · show cn (l * q 3 + ξ (q 3) * h) ≤ fthr 3
    rw [fev_identity ξ h l hq]
    have hf3 : fthr 3 = 1 / 10 := by simp [fthr]
    rw [hf3]
    have t1 := cn_sub_le ((l * q 0 + ξ (q 0) * h) + (l * q 1 + ξ (q 1) * h) -
      (l * q 2 + ξ (q 2) * h)) (sig ξ q * h)
    have t2 := cn_sub_le ((l * q 0 + ξ (q 0) * h) + (l * q 1 + ξ (q 1) * h))
      (l * q 2 + ξ (q 2) * h)
    have t3 := cn_add_le (l * q 0 + ξ (q 0) * h) (l * q 1 + ξ (q 1) * h)
    linarith

/-- A very bad quadruple survives a filter with probability at most about `10⁻⁶/2`. -/
theorem fprob_bad (hp : p.Prime) {S : Finset (ZMod p)} {ρh ρv : ℝ} (hρh : 0 < ρh) (hρv : 0 < ρv)
    (h4 : 2 * ρv ≤ ρh) {m : ℕ} (hm : 1 ≤ m)
    (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p) (ξ : ZMod p → ZMod p) {q : Fin 4 → ZMod p}
    (hq : q 0 + q 1 = q 2 + q 3) (hb : ¬ Good S (1 / ρv) (sig ξ q)) (hgen : gen3 (gM m) q) :
    fprob S ρh ξ q ≤ (1 / 2 + 50 * S.card * (ρv / 2) / ρh / 2) *
      ((1 / 10 ^ 6 : ℝ) * (1 + 1 / (4 * m))) := by
  classical
  have hP := regP_isDist S hρh.le
  have hhalf := prob_small_le_half hρh hρv h4 hb
  set B : ℝ := (1 / 10 ^ 6 : ℝ) * (1 + 1 / (4 * m)) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hpt : ∀ h, ∑ l, (1 / p : ℝ) * (if fev ξ h l q then 1 else 0) ≤
      (if cn (sig ξ q * h) ≤ 1 / 8 then 1 else 0) * B := by
    intro h
    have hb := (boxP_unif hp hm hpm ![q 0, q 1, q 2] (fun i => ξ (![q 0, q 1, q 2] i) * h) hgen).2
    rw [boxP_eq_three] at hb
    split_ifs with hs
    · rw [one_mul]
      refine le_trans (sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (by positivity)) hb
      split_ifs with h1 h2 <;> try norm_num
      exact h2 ⟨by simpa [fthr] using h1 0, by simpa [fthr] using h1 1, by simpa [fthr] using h1 2⟩
    · rw [zero_mul]
      refine le_of_eq (sum_eq_zero fun l _ => ?_)
      rw [if_neg, mul_zero]
      intro H
      apply hs
      have a := H 0; have b := H 1; have c := H 2; have d := H 3
      have hf0 : fthr 0 = 1 / 200 := by simp [fthr]
      have hf1 : fthr 1 = 1 / 200 := by simp [fthr]
      have hf2 : fthr 2 = 1 / 200 := by simp [fthr]
      have hf3 : fthr 3 = 1 / 10 := by simp [fthr]
      rw [hf0] at a; rw [hf1] at b; rw [hf2] at c; rw [hf3] at d
      have e : sig ξ q * h = (l * q 0 + ξ (q 0) * h) + (l * q 1 + ξ (q 1) * h) -
          (l * q 2 + ξ (q 2) * h) - (l * q 3 + ξ (q 3) * h) := by
        rw [fev_identity ξ h l hq]; ring
      rw [e]
      have t1 := cn_sub_le ((l * q 0 + ξ (q 0) * h) + (l * q 1 + ξ (q 1) * h) -
        (l * q 2 + ξ (q 2) * h)) (l * q 3 + ξ (q 3) * h)
      have t2 := cn_sub_le ((l * q 0 + ξ (q 0) * h) + (l * q 1 + ξ (q 1) * h))
        (l * q 2 + ξ (q 2) * h)
      have t3 := cn_add_le (l * q 0 + ξ (q 0) * h) (l * q 1 + ξ (q 1) * h)
      linarith
  unfold fprob
  calc ∑ h, regP S ρh h * ∑ l, (1 / p : ℝ) * (if fev ξ h l q then 1 else 0)
      ≤ ∑ h, regP S ρh h * ((if cn (sig ξ q * h) ≤ 1 / 8 then 1 else 0) * B) :=
        sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hpt h) (hP.1 h)
    _ = (∑ h, regP S ρh h * (if cn (sig ξ q * h) ≤ 1 / 8 then 1 else 0)) * B := by
        rw [sum_mul]; exact sum_congr rfl fun h _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hhalf hB0

lemma fprob_nonneg (S : Finset (ZMod p)) (ρh : ℝ) (ξ : ZMod p → ZMod p) (q : Fin 4 → ZMod p) :
    0 ≤ fprob S ρh ξ q := by
  unfold fprob
  refine sum_nonneg fun h _ => mul_nonneg (regP_nonneg _ _) (sum_nonneg fun l _ =>
    mul_nonneg (by positivity) (by split_ifs <;> norm_num))

lemma fprob_le_one {S : Finset (ZMod p)} {ρh : ℝ} (hρh : 0 ≤ ρh) (ξ : ZMod p → ZMod p)
    (q : Fin 4 → ZMod p) : fprob S ρh ξ q ≤ 1 := by
  classical
  have hP := regP_isDist S hρh
  unfold fprob
  refine wavg_le hP.1 hP.2 _ fun h _ => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  calc ∑ l, (1 / p : ℝ) * (if fev ξ h l q then 1 else 0) ≤ ∑ _l : ZMod p, (1 / p : ℝ) :=
        sum_le_sum fun l _ => by split_ifs <;> simp
    _ = 1 := by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; field_simp

/-! ### Non-generic quadruples are rare -/

lemma sum_lin_single_le (hp : p.Prime) {P : ZMod p → ℝ} (hP : ∀ x, 0 ≤ P x) {B : ℝ}
    (hB : ∀ x, P x ≤ B) {a : ZMod p} (ha : a ≠ 0) (e b : ZMod p) :
    ∑ x, P x * (if a * x + e = b then 1 else 0) ≤ B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hiff : ∀ x, (a * x + e = b) ↔ (x = a⁻¹ * (b - e)) := fun x => by
    constructor
    · intro h; rw [← h]; field_simp; ring
    · intro h; rw [h]; field_simp; ring
  simp_rw [hiff, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq']
  simp only [mem_univ, if_true]
  exact hB _

lemma prob_lin_eq_le (hp : p.Prime) {P2 P3 P4 : ZMod p → ℝ} (h2 : ∀ x, 0 ≤ P2 x)
    (h2' : ∑ x, P2 x = 1) (h3 : ∀ x, 0 ≤ P3 x) (h3' : ∑ x, P3 x = 1) (h4 : ∀ x, 0 ≤ P4 x)
    (h4' : ∑ x, P4 x = 1) {B : ℝ} (hB2 : ∀ x, P2 x ≤ B) (hB3 : ∀ x, P3 x ≤ B)
    (hB4 : ∀ x, P4 x ≤ B) (a2 a3 a4 b : ZMod p) (hne : a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0) :
    ∑ x2, ∑ x3, ∑ x4, P2 x2 * P3 x3 * P4 x4 *
      (if a2 * x2 + a3 * x3 + a4 * x4 = b then 1 else 0) ≤ B := by
  classical
  rcases hne with ha | ha | ha
  · -- `x2` innermost
    have e : ∑ x2, ∑ x3, ∑ x4, P2 x2 * P3 x3 * P4 x4 *
        (if a2 * x2 + a3 * x3 + a4 * x4 = b then 1 else 0) =
        ∑ x3, P3 x3 * ∑ x4, P4 x4 * ∑ x2, P2 x2 *
          (if a2 * x2 + (a3 * x3 + a4 * x4) = b then 1 else 0) := by
      simp only [mul_sum]
      rw [sum_comm]; refine sum_congr rfl fun x3 _ => ?_
      rw [sum_comm]; refine sum_congr rfl fun x4 _ => sum_congr rfl fun x2 _ => ?_
      rw [show a2 * x2 + a3 * x3 + a4 * x4 = a2 * x2 + (a3 * x3 + a4 * x4) by ring]; ring
    rw [e]
    refine wavg_le h3 h3' _ fun x3 _ => wavg_le h4 h4' _ fun x4 _ => ?_
    exact sum_lin_single_le hp h2 hB2 ha _ _
  · have e : ∑ x2, ∑ x3, ∑ x4, P2 x2 * P3 x3 * P4 x4 *
        (if a2 * x2 + a3 * x3 + a4 * x4 = b then 1 else 0) =
        ∑ x2, P2 x2 * ∑ x4, P4 x4 * ∑ x3, P3 x3 *
          (if a3 * x3 + (a2 * x2 + a4 * x4) = b then 1 else 0) := by
      simp only [mul_sum]
      refine sum_congr rfl fun x2 _ => ?_
      rw [sum_comm]; refine sum_congr rfl fun x4 _ => sum_congr rfl fun x3 _ => ?_
      rw [show a2 * x2 + a3 * x3 + a4 * x4 = a3 * x3 + (a2 * x2 + a4 * x4) by ring]; ring
    rw [e]
    refine wavg_le h2 h2' _ fun x2 _ => wavg_le h4 h4' _ fun x4 _ => ?_
    exact sum_lin_single_le hp h3 hB3 ha _ _
  · have e : ∑ x2, ∑ x3, ∑ x4, P2 x2 * P3 x3 * P4 x4 *
        (if a2 * x2 + a3 * x3 + a4 * x4 = b then 1 else 0) =
        ∑ x2, P2 x2 * ∑ x3, P3 x3 * ∑ x4, P4 x4 *
          (if a4 * x4 + (a2 * x2 + a3 * x3) = b then 1 else 0) := by
      simp only [mul_sum]
      refine sum_congr rfl fun x2 _ => sum_congr rfl fun x3 _ => sum_congr rfl fun x4 _ => ?_
      rw [show a2 * x2 + a3 * x3 + a4 * x4 = a4 * x4 + (a2 * x2 + a3 * x3) by ring]; ring
    rw [e]
    refine wavg_le h2 h2' _ fun x2 _ => wavg_le h3 h3' _ fun x3 _ => ?_
    exact sum_lin_single_le hp h4 hB4 ha _ _

lemma intCast_ne_zero_of_abs_lt {k : ℤ} (hk : k ≠ 0) (hkp : |k| < p) : (k : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact hk (Int.eq_zero_of_abs_lt_dvd h hkp)

/-- The box of small integer vectors. -/
def kbox (M : ℕ) : Finset (Fin 3 → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(2 * M : ℤ) + 1) (2 * M - 1)).filter (· ≠ 0)

lemma card_kbox (M : ℕ) : ((kbox M).card : ℝ) ≤ (4 * M) ^ 3 := by
  unfold kbox
  have h1 : (((Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(2 * M : ℤ) + 1) (2 * M - 1)).filter
      (· ≠ 0)).card : ℝ) ≤ (Fintype.piFinset fun _ : Fin 3 =>
        Finset.Icc (-(2 * M : ℤ) + 1) (2 * M - 1)).card := by
    exact_mod_cast card_filter_le _ _
  refine h1.trans ?_
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, Int.card_Icc]
  push_cast
  gcongr
  have : (2 * (M : ℤ) - 1 + 1 - (-(2 * M) + 1)).toNat ≤ 4 * M := by omega
  exact_mod_cast this

lemma mem_kbox {M : ℕ} {k : Fin 3 → ℤ} (hk : k ≠ 0) (hkM : ∀ i, |k i| < 2 * M) : k ∈ kbox M := by
  unfold kbox
  rw [mem_filter, Fintype.mem_piFinset]
  refine ⟨fun i => ?_, hk⟩
  have := hkM i
  rw [abs_lt] at this
  rw [Finset.mem_Icc]; constructor <;> omega

open Classical in
/-- Non-generic quadruples have small mass under a centred random quadruple. -/
theorem qavg_nongen (hp : p.Prime) {S : Finset (ZMod p)} {r2 r3 r4 : ℝ} (hr2 : 0 < r2)
    (h23 : r2 ≤ r3) (h34 : r3 ≤ r4) (hr4 : r4 ≤ 1) {M : ℕ} (hMp : 2 * M ≤ p)
    (c : Fin 4 → ZMod p) :
    qavg S r2 r3 r4 c (fun q => if gen3 M q then 0 else 1) ≤
      (4 * M) ^ 3 * (1 / (p * (r2 / 4) ^ S.card)) := by
  classical
  have hr3 : 0 < r3 := by linarith
  have hr4' : 0 < r4 := by linarith
  have hP2 := regP_isDist S hr2.le
  have hP3 := regP_isDist S hr3.le
  have hP4 := regP_isDist S hr4'.le
  set B : ℝ := 1 / (p * (r2 / 4) ^ S.card) with hB
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hBmono : ∀ {r : ℝ}, r2 ≤ r → r ≤ 1 → ∀ x, regP S r x ≤ B := by
    intro r hr hr1 x
    refine (regP_le S (by linarith) hr1 x).trans ?_
    rw [hB]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) hp0.le)
  -- union bound
  have hpt : ∀ q : Fin 4 → ZMod p, (if gen3 M q then (0 : ℝ) else 1) ≤
      ∑ k ∈ kbox M, (if zdot k ![q 0, q 1, q 2] = 0 then 1 else 0) := by
    intro q
    split_ifs with hg
    · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num
    · unfold gen3 at hg
      push_neg at hg
      obtain ⟨k, hk0, hkM, hz⟩ := hg
      calc (1 : ℝ) = if zdot k ![q 0, q 1, q 2] = 0 then 1 else 0 := by rw [if_pos hz]
        _ ≤ _ := single_le_sum (f := fun k => if zdot k ![q 0, q 1, q 2] = 0 then (1 : ℝ) else 0)
            (fun _ _ => by (try dsimp only); split_ifs <;> norm_num) (mem_kbox hk0 hkM)
  have hq : ∀ k ∈ kbox M, qavg S r2 r3 r4 c (fun q => if zdot k ![q 0, q 1, q 2] = 0 then 1 else 0)
      ≤ B := by
    intro k hk
    unfold kbox at hk
    rw [mem_filter, Fintype.mem_piFinset] at hk
    obtain ⟨hkI, hk0⟩ := hk
    have habs : ∀ i, |k i| < p := fun i => by
      have := hkI i
      rw [Finset.mem_Icc] at this
      rw [abs_lt]; constructor <;> omega
    have e : ∀ x2 x3 x4 : ZMod p, zdot k ![qd c x2 x3 x4 0, qd c x2 x3 x4 1, qd c x2 x3 x4 2] =
        ((k 1 : ZMod p) - k 0) * x2 + ((k 0 : ZMod p) + k 2) * x3 + (k 0 : ZMod p) * x4 +
          ((k 0 : ZMod p) * (c 2 + c 3 - c 1) + k 1 * c 1 + k 2 * c 2) := by
      intro x2 x3 x4
      simp only [zdot, Fin.sum_univ_three, qd, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    unfold qavg
    simp_rw [e]
    have e2 : ∀ x2 x3 x4 : ZMod p, (if ((k 1 : ZMod p) - k 0) * x2 + ((k 0 : ZMod p) + k 2) * x3 +
        (k 0 : ZMod p) * x4 + ((k 0 : ZMod p) * (c 2 + c 3 - c 1) + k 1 * c 1 + k 2 * c 2) = 0
        then (1 : ℝ) else 0) = if ((k 1 : ZMod p) - k 0) * x2 + ((k 0 : ZMod p) + k 2) * x3 +
        (k 0 : ZMod p) * x4 = -((k 0 : ZMod p) * (c 2 + c 3 - c 1) + k 1 * c 1 + k 2 * c 2)
        then 1 else 0 := by
      intro x2 x3 x4
      congr 1
      apply propext; constructor <;> intro h <;> linear_combination h
    simp_rw [e2]
    refine prob_lin_eq_le hp hP2.1 hP2.2 hP3.1 hP3.2 hP4.1 hP4.2 (hBmono le_rfl (by linarith))
      (hBmono h23 (by linarith)) (hBmono (by linarith) hr4) _ _ _ _ ?_
    by_cases h0 : k 0 = 0
    · by_cases h2 : k 2 = 0
      · left
        have h1 : k 1 ≠ 0 := by
          intro h1; apply hk0; funext i; fin_cases i <;> simp [h0, h1, h2]
        rw [h0]; push_cast; rw [sub_zero]
        exact intCast_ne_zero_of_abs_lt h1 (habs 1)
      · right; left
        rw [h0]; push_cast; rw [zero_add]
        exact intCast_ne_zero_of_abs_lt h2 (habs 2)
    · right; right
      exact intCast_ne_zero_of_abs_lt h0 (habs 0)
  -- assemble
  have hqavg_mono : ∀ F G : (Fin 4 → ZMod p) → ℝ, (∀ q, F q ≤ G q) →
      qavg S r2 r3 r4 c F ≤ qavg S r2 r3 r4 c G := by
    intro F G hFG
    unfold qavg
    exact sum_le_sum fun x2 _ => sum_le_sum fun x3 _ => sum_le_sum fun x4 _ =>
      mul_le_mul_of_nonneg_left (hFG _)
        (mul_nonneg (mul_nonneg (hP2.1 _) (hP3.1 _)) (hP4.1 _))
  have hqavg_sum : qavg S r2 r3 r4 c (fun q => ∑ k ∈ kbox M,
      (if zdot k ![q 0, q 1, q 2] = 0 then (1 : ℝ) else 0)) = ∑ k ∈ kbox M,
      qavg S r2 r3 r4 c (fun q => if zdot k ![q 0, q 1, q 2] = 0 then 1 else 0) := by
    unfold qavg
    simp only [mul_sum]
    symm
    rw [Finset.sum_comm]; refine sum_congr rfl fun x2 _ => ?_
    rw [Finset.sum_comm]; refine sum_congr rfl fun x3 _ => ?_
    rw [Finset.sum_comm]
  calc qavg S r2 r3 r4 c (fun q => if gen3 M q then 0 else 1)
      ≤ ∑ k ∈ kbox M, qavg S r2 r3 r4 c (fun q => if zdot k ![q 0, q 1, q 2] = 0 then 1 else 0) := by
        rw [← hqavg_sum]; exact hqavg_mono _ _ hpt
    _ ≤ ∑ _k ∈ kbox M, B := sum_le_sum hq
    _ = (kbox M).card * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (4 * M) ^ 3 * B := mul_le_mul_of_nonneg_right (card_kbox M) (by positivity)

/-! ### Many filters -/

lemma filt_arith {m : ℕ} (hm : 1 ≤ m) {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / (4 * m)) :
    (3 / 4) * (1 / 10 ^ 6 : ℝ) ^ m ≤ ((1 / 10 ^ 6) * (1 - 1 / (4 * m))) ^ m ∧
      ((1 / 2 + e / 2) * ((1 / 10 ^ 6) * (1 + 1 / (4 * m)))) ^ m ≤
        2 * (1 / 2 : ℝ) ^ m * (1 / 10 ^ 6 : ℝ) ^ m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  constructor
  · rw [mul_pow]
    have hb := one_add_mul_le_pow (a := -(1 / (4 * (m : ℝ)))) (by
      have : 1 / (4 * (m : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith) m
    have e1 : 1 + (m : ℝ) * -(1 / (4 * m)) = 3 / 4 := by field_simp; ring
    rw [e1, ← sub_eq_add_neg] at hb
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  · have e1 : (1 / 2 + e / 2) * ((1 / 10 ^ 6 : ℝ) * (1 + 1 / (4 * m))) =
        (1 / 2) * (1 / 10 ^ 6) * ((1 + e) * (1 + 1 / (4 * m))) := by ring
    rw [e1, mul_pow, mul_pow, mul_pow]
    have h1 : (1 + e) ^ m ≤ Real.exp (1 / 4) := by
      calc (1 + e) ^ m ≤ (Real.exp e) ^ m :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp e]) m
        _ = Real.exp (m * e) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (1 / 4) := Real.exp_le_exp.2 (by
            rw [le_div_iff₀ (by positivity)] at he
            nlinarith)
    have h2 : (1 + 1 / (4 * (m : ℝ))) ^ m ≤ Real.exp (1 / 4) := by
      calc (1 + 1 / (4 * (m : ℝ))) ^ m ≤ (Real.exp (1 / (4 * m))) ^ m :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (4 * (m : ℝ)))]) m
        _ = Real.exp (m * (1 / (4 * m))) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (1 / 4) := by congr 1; field_simp
    have h3 : Real.exp (1 / 4) * Real.exp (1 / 4) ≤ 2 := by
      rw [← Real.exp_add]
      have := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 4 + 1 / 4) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 4 + 1 / 4)]
    have h12 : (1 + e) ^ m * (1 + 1 / (4 * (m : ℝ))) ^ m ≤ 2 :=
      (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le).trans h3
    have hpos : (0 : ℝ) ≤ (1 / 2) ^ m * (1 / 10 ^ 6) ^ m := by positivity
    calc (1 / 2 : ℝ) ^ m * (1 / 10 ^ 6) ^ m * ((1 + e) ^ m * (1 + 1 / (4 * m)) ^ m)
        ≤ (1 / 2) ^ m * (1 / 10 ^ 6) ^ m * 2 := mul_le_mul_of_nonneg_left h12 hpos
      _ = _ := by ring

/-- The sets cut out by a family of filters. -/
def fset (ξ : ZMod p → ZMod p) (Ω : Finset (ZMod p)) {m : ℕ} (Φ : Fin m → ZMod p × ZMod p)
    (i : Fin 4) : Finset (ZMod p) :=
  Ω.filter fun n => ∀ j, cn ((Φ j).2 * n + ξ n * (Φ j).1) ≤ fthr i

lemma qavg_mono' {S : Finset (ZMod p)} {r2 r3 r4 : ℝ} (hr2 : 0 ≤ r2) (hr3 : 0 ≤ r3)
    (hr4 : 0 ≤ r4) (c : Fin 4 → ZMod p) {F G : (Fin 4 → ZMod p) → ℝ}
    (h : ∀ x2 x3 x4, F (qd c x2 x3 x4) ≤ G (qd c x2 x3 x4)) :
    qavg S r2 r3 r4 c F ≤ qavg S r2 r3 r4 c G := by
  unfold qavg
  exact sum_le_sum fun x2 _ => sum_le_sum fun x3 _ => sum_le_sum fun x4 _ =>
    mul_le_mul_of_nonneg_left (h _ _ _) (mul_nonneg (mul_nonneg (regP_nonneg _ _)
      (regP_nonneg _ _)) (regP_nonneg _ _))

lemma qavg_add (S : Finset (ZMod p)) (r2 r3 r4 : ℝ) (c : Fin 4 → ZMod p)
    (F G : (Fin 4 → ZMod p) → ℝ) :
    qavg S r2 r3 r4 c (fun q => F q + G q) = qavg S r2 r3 r4 c F + qavg S r2 r3 r4 c G := by
  unfold qavg
  simp only [mul_add, sum_add_distrib]

lemma qavg_smul (S : Finset (ZMod p)) (r2 r3 r4 : ℝ) (c : Fin 4 → ZMod p) (a : ℝ)
    (F : (Fin 4 → ZMod p) → ℝ) :
    qavg S r2 r3 r4 c (fun q => a * F q) = a * qavg S r2 r3 r4 c F := by
  unfold qavg
  simp only [mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

end

end GT
end File_GT_U3S3

section File_GT_U3S3b
/-!
# Local inverse `U³`, third step (Green–Tao, Theorem 9.4)

Averaging over `m` independent random filters.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The weight of a single filter `(h, λ)`. -/
def fw (S : Finset (ZMod p)) (ρh : ℝ) (φ : ZMod p × ZMod p) : ℝ := regP S ρh φ.1 * (1 / p)

lemma fw_isDist (S : Finset (ZMod p)) {ρh : ℝ} (hρh : 0 ≤ ρh) :
    (∀ φ, 0 ≤ fw S ρh φ) ∧ ∑ φ, fw S ρh φ = 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  refine ⟨fun φ => mul_nonneg (regP_nonneg _ _) (by positivity), ?_⟩
  unfold fw
  rw [Fintype.sum_prod_type]
  simp only [← mul_sum, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  rw [← sum_mul, sum_regP S hρh]
  field_simp

open Classical in
lemma fprob_eq (S : Finset (ZMod p)) (ρh : ℝ) (ξ : ZMod p → ZMod p) (q : Fin 4 → ZMod p) :
    fprob S ρh ξ q = ∑ φ : ZMod p × ZMod p, fw S ρh φ * (if fev ξ φ.1 φ.2 q then 1 else 0) := by
  unfold fprob fw
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun h _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun l _ => by ring

lemma fwm_isDist (S : Finset (ZMod p)) {ρh : ℝ} (hρh : 0 ≤ ρh) (m : ℕ) :
    (∀ Φ : Fin m → ZMod p × ZMod p, 0 ≤ ∏ j, fw S ρh (Φ j)) ∧
      ∑ Φ : Fin m → ZMod p × ZMod p, ∏ j, fw S ρh (Φ j) = 1 := by
  refine ⟨fun Φ => prod_nonneg fun j _ => (fw_isDist S hρh).1 _, ?_⟩
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp [(fw_isDist S hρh).2]

open Classical in
lemma favg (S : Finset (ZMod p)) (ρh : ℝ) (ξ : ZMod p → ZMod p) (Ω : Finset (ZMod p)) (m : ℕ)
    (q : Fin 4 → ZMod p) :
    ∑ Φ : Fin m → ZMod p × ZMod p, (∏ j, fw S ρh (Φ j)) *
      (if ∀ i, q i ∈ fset ξ Ω Φ i then 1 else 0) =
      (if ∀ i, q i ∈ Ω then 1 else 0) * fprob S ρh ξ q ^ m := by
  have hpt : ∀ Φ : Fin m → ZMod p × ZMod p, (if ∀ i, q i ∈ fset ξ Ω Φ i then (1 : ℝ) else 0) =
      (if ∀ i, q i ∈ Ω then 1 else 0) * ∏ j, (if fev ξ (Φ j).1 (Φ j).2 q then 1 else 0) := by
    intro Φ
    rw [prod_boole]
    simp only [fset, mem_filter]
    by_cases hΩ : ∀ i, q i ∈ Ω
    · rw [if_pos hΩ, one_mul]
      congr 1
      apply propext
      constructor
      · intro H j _ i; exact (H i).2 j
      · intro H i; exact ⟨hΩ i, fun j => H j (mem_univ _) i⟩
    · rw [if_neg hΩ, zero_mul, if_neg]
      intro H; exact hΩ fun i => (H i).1
  simp_rw [hpt]
  have e : ∀ Φ : Fin m → ZMod p × ZMod p, (∏ j, fw S ρh (Φ j)) * ((if ∀ i, q i ∈ Ω then (1 : ℝ)
      else 0) * ∏ j, (if fev ξ (Φ j).1 (Φ j).2 q then 1 else 0)) =
      (if ∀ i, q i ∈ Ω then 1 else 0) *
        ∏ j, (fw S ρh (Φ j) * (if fev ξ (Φ j).1 (Φ j).2 q then 1 else 0)) := fun Φ => by
    rw [prod_mul_distrib]; ring
  simp_rw [e, ← mul_sum]
  congr 1
  rw [fprob_eq, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma qavg_const {S : Finset (ZMod p)} {r2 r3 r4 : ℝ} (hr2 : 0 ≤ r2) (hr3 : 0 ≤ r3)
    (hr4 : 0 ≤ r4) (c : Fin 4 → ZMod p) (a : ℝ) : qavg S r2 r3 r4 c (fun _ => a) = a := by
  unfold qavg
  simp only [← sum_mul, ← mul_sum, sum_regP S hr2, sum_regP S hr3, sum_regP S hr4, mul_one,
    one_mul]

lemma qavg_lin3 {S : Finset (ZMod p)} {r2 r3 r4 : ℝ} (hr2 : 0 ≤ r2) (hr3 : 0 ≤ r3)
    (hr4 : 0 ≤ r4) (c : Fin 4 → ZMod p) (a b d : ℝ) (F G : (Fin 4 → ZMod p) → ℝ) :
    qavg S r2 r3 r4 c (fun q => a * F q + b * G q + d) =
      a * qavg S r2 r3 r4 c F + b * qavg S r2 r3 r4 c G + d := by
  rw [qavg_add S r2 r3 r4 c (fun q => a * F q + b * G q) (fun _ => d),
    qavg_add S r2 r3 r4 c (fun q => a * F q) (fun q => b * G q), qavg_smul, qavg_smul,
    qavg_const hr2 hr3 hr4]

lemma qavg_swap {S : Finset (ZMod p)} {r2 r3 r4 : ℝ} (c : Fin 4 → ZMod p) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → (Fin 4 → ZMod p) → ℝ) :
    ∑ j, w j * qavg S r2 r3 r4 c (F j) = qavg S r2 r3 r4 c (fun q => ∑ j, w j * F j q) := by
  unfold qavg
  simp only [mul_sum]
  rw [Finset.sum_comm]; refine sum_congr rfl fun x2 _ => ?_
  rw [Finset.sum_comm]; refine sum_congr rfl fun x3 _ => ?_
  rw [Finset.sum_comm]; refine sum_congr rfl fun x4 _ => sum_congr rfl fun j _ => by ring

lemma step3_arith {X cG L NG b g B : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hcG : 0 ≤ cG) (hL : 1 ≤ L)
    (hb : 3 / 4 * X ≤ b) (hbX : b ≤ X) (hg : L * g ≤ X * cG / 8)
    (hNG0 : 0 ≤ NG) (hNG : NG ≤ X * cG / (8 * L)) (hB : cG ≤ B) :
    X * cG / 4 ≤ b * B - (b + L) * NG - L * g := by
  have hL0 : 0 < L := by linarith
  have h1 : (b + L) * NG ≤ X * cG / 4 := by
    have : (b + L) * NG ≤ (b + L) * (X * cG / (8 * L)) :=
      mul_le_mul_of_nonneg_left hNG (by nlinarith)
    have e : (b + L) * (X * cG / (8 * L)) = (b / L + 1) * (X * cG) / 8 := by field_simp
    have hbL : b / L ≤ 1 := by rw [div_le_one hL0]; linarith
    have hXc : 0 ≤ X * cG := mul_nonneg hX0 hcG
    nlinarith
  have h2 : b * cG ≤ b * B := mul_le_mul_of_nonneg_left hB (by linarith)
  nlinarith [mul_nonneg hX0 hcG]

open Classical in
lemma step3_pointwise {S : Finset (ZMod p)} {Ω : Finset (ZMod p)} {ξ : ZMod p → ZMod p}
    {ρv A L b g f : ℝ} {q : Fin 4 → ZMod p} {gen : Prop} (hL : 1 ≤ L) (hAv : A ≤ 1 / ρv)
    (hb0 : 0 ≤ b) (hg0 : 0 ≤ g) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hfg : gen → (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) → b ≤ f)
    (hfb : gen → ¬ Good S (1 / ρv) (sig ξ q) → f ≤ g) :
    b * (if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0) -
      (b + L) * (if gen then 0 else 1) - L * g ≤
      (if ∀ i, q i ∈ Ω then 1 else 0) * f *
        (1 - L * (if Good S (1 / ρv) (sig ξ q) then 0 else 1)) := by
  have hLg : 0 ≤ L * g := mul_nonneg (by linarith) hg0
  by_cases hgen : gen
  · rw [if_pos hgen, mul_zero, sub_zero]
    by_cases hvb : Good S (1 / ρv) (sig ξ q)
    · rw [if_pos hvb, mul_zero, sub_zero, mul_one]
      by_cases hgood : (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q)
      · rw [if_pos hgood, if_pos hgood.1, one_mul, mul_one]
        have := hfg hgen hgood
        linarith
      · rw [if_neg hgood, mul_zero]
        have : 0 ≤ (if ∀ i, q i ∈ Ω then (1 : ℝ) else 0) * f :=
          mul_nonneg (by split_ifs <;> norm_num) hf0
        linarith
    · rw [if_neg hvb, mul_one]
      have hgoodF : ¬ ((∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q)) := fun h => hvb (h.2.mono hAv)
      rw [if_neg hgoodF, mul_zero, zero_sub]
      have hfg' := hfb hgen hvb
      have hI0 : (0 : ℝ) ≤ if ∀ i, q i ∈ Ω then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      have hI1 : (if ∀ i, q i ∈ Ω then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have h1 : (if ∀ i, q i ∈ Ω then (1 : ℝ) else 0) * f ≤ f := mul_le_of_le_one_left hf0 hI1
      have h2 : f * (1 - L) ≤ (if ∀ i, q i ∈ Ω then (1 : ℝ) else 0) * f * (1 - L) :=
        mul_le_mul_of_nonpos_right h1 (by linarith)
      have h3 : L * f ≤ L * g := mul_le_mul_of_nonneg_left hfg' (by linarith)
      nlinarith
  · rw [if_neg hgen, mul_one]
    have hI0 : (0 : ℝ) ≤ if ∀ i, q i ∈ Ω then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    have hI1 : (if ∀ i, q i ∈ Ω then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have hV0 : (0 : ℝ) ≤ if Good S (1 / ρv) (sig ξ q) then 0 else 1 := by split_ifs <;> norm_num
    have hV1 : (if Good S (1 / ρv) (sig ξ q) then (0 : ℝ) else 1) ≤ 1 := by split_ifs <;> norm_num
    have hG1 : (if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    set I := (if ∀ i, q i ∈ Ω then (1 : ℝ) else 0)
    set V := (if Good S (1 / ρv) (sig ξ q) then (0 : ℝ) else 1)
    set G := (if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then (1 : ℝ) else 0)
    have ha0 : 0 ≤ I * f := mul_nonneg hI0 hf0
    have ha1 : I * f ≤ 1 := by nlinarith
    have hk : 1 - L ≤ 1 - L * V := by nlinarith
    have h4 : I * f * (1 - L) ≤ I * f * (1 - L * V) := mul_le_mul_of_nonneg_left hk ha0
    have h5 : (1 - L) ≤ I * f * (1 - L) := by nlinarith
    have h6 : b * G ≤ b := mul_le_of_le_one_right hb0 hG1
    linarith

open Classical in
/-- **Theorem 9.4** (third step): sets `A₁, …, A₄ ⊆ Ω` on which very bad quadruples are rare. -/
theorem u3_step3 (hp : p.Prime) {S : Finset (ZMod p)} {r2 r3 r4 ρh ρv A cG L : ℝ}
    (hr2 : 0 < r2) (h23 : r2 ≤ r3) (h34 : r3 ≤ r4) (hr4 : r4 ≤ 1)
    (hρh : 0 < ρh) (hρv : 0 < ρv) (h2v : 2 * ρv ≤ ρh)
    (hA0 : 0 ≤ A) (hAρ : A * ρh ≤ 1 / 1000) (hAv : A ≤ 1 / ρv) (hcG : 0 ≤ cG)
    (hL : 1 ≤ L) {m : ℕ} (hm : 1 ≤ m) (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p)
    (he : 50 * S.card * (ρv / 2) / ρh ≤ 1 / (4 * m))
    (hmL : 16 * L ≤ 2 ^ m * cG)
    (hNG : (4 * (gM m : ℝ)) ^ 3 * (1 / (p * (r2 / 4) ^ S.card)) ≤ (1 / 10 ^ 6) ^ m * cG / (8 * L))
    (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (c : Fin 4 → ZMod p)
    (hG : cG ≤ qavg S r2 r3 r4 c
      (fun q => if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0)) :
    ∃ As : Fin 4 → Finset (ZMod p), (∀ i, As i ⊆ Ω) ∧
      (1 / 10 ^ 6) ^ m * cG / 4 ≤ qavg S r2 r3 r4 c (Wt S ρv L ξ As) := by
  have hr3 : 0 < r3 := by linarith
  have hr4' : 0 < r4 := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set e : ℝ := 50 * S.card * (ρv / 2) / ρh with he_def
  have he0 : 0 ≤ e := by rw [he_def]; positivity
  set β : ℝ := (1 / 10 ^ 6) * (1 - 1 / (4 * m)) with hβ
  set γ : ℝ := (1 / 2 + e / 2) * ((1 / 10 ^ 6) * (1 + 1 / (4 * m))) with hγ
  obtain ⟨hβm, hγm⟩ := filt_arith hm he0 he
  have hβ0 : 0 ≤ β := by
    rw [hβ]; have : 1 / (4 * (m : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hβ1 : β ≤ 1 / 10 ^ 6 := by
    rw [hβ]; have : 0 ≤ 1 / (4 * (m : ℝ)) := by positivity
    nlinarith
  have hp2m : (0 : ℝ) < 2 ^ m := by positivity
  -- expected weight
  set EW : (Fin 4 → ZMod p) → ℝ := fun q => (if ∀ i, q i ∈ Ω then 1 else 0) *
    fprob S ρh ξ q ^ m * (1 - L * (if Good S (1 / ρv) (sig ξ q) then 0 else 1)) with hEW
  have hwm := fwm_isDist S hρh.le m
  have hclaim1 : ∑ Φ : Fin m → ZMod p × ZMod p, (∏ j, fw S ρh (Φ j)) *
      qavg S r2 r3 r4 c (Wt S ρv L ξ (fset ξ Ω Φ)) = qavg S r2 r3 r4 c EW := by
    rw [qavg_swap]
    congr 1
    funext q
    have := favg S ρh ξ Ω m q
    simp only [Wt, hEW]
    rw [← this, sum_mul]
    exact sum_congr rfl fun Φ _ => by ring
  -- pointwise lower bound
  set LB : (Fin 4 → ZMod p) → ℝ := fun q =>
    β ^ m * (if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0) -
      (β ^ m + L) * (if gen3 (gM m) q then 0 else 1) - L * γ ^ m with hLB
  have hpt : ∀ x2 x3 x4, LB (qd c x2 x3 x4) ≤ EW (qd c x2 x3 x4) := by
    intro x2 x3 x4
    have hadd := qd_add c x2 x3 x4
    have hf0 := fprob_nonneg S ρh ξ (qd c x2 x3 x4)
    have hf1 := fprob_le_one (S := S) hρh.le ξ (qd c x2 x3 x4)
    simp only [hLB, hEW]
    exact step3_pointwise hL hAv (pow_nonneg hβ0 m) (by rw [hγ]; positivity)
      (pow_nonneg hf0 m) (pow_le_one₀ hf0 hf1)
      (fun hgen hgood => pow_le_pow_left₀ hβ0
        (fprob_good hp hρh hAρ hA0 hm hpm ξ hadd hgood.2 hgen) m)
      (fun hgen hvb => pow_le_pow_left₀ hf0 (fprob_bad hp hρh hρv h2v hm hpm ξ hadd hvb hgen) m)
  -- average the lower bound
  have hNGq := qavg_nongen hp (S := S) hr2 h23 h34 hr4 (M := gM m) (by
    have hgM : (gM m : ℝ) = 2 * 10 ^ 12 * m ^ 2 := by unfold gM; push_cast; ring
    have hm2 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 10 := pow_le_pow_right₀ hm1 (by norm_num)
    have : (2 * gM m : ℝ) ≤ p := by rw [hgM]; nlinarith
    exact_mod_cast this) c
  have hLBq : qavg S r2 r3 r4 c LB = β ^ m * qavg S r2 r3 r4 c
      (fun q => if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0) -
      (β ^ m + L) * qavg S r2 r3 r4 c (fun q => if gen3 (gM m) q then 0 else 1) - L * γ ^ m := by
    have e1 : LB = fun q => β ^ m * (if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0) +
        (-(β ^ m + L)) * (if gen3 (gM m) q then 0 else 1) + (-(L * γ ^ m)) := by
      rw [hLB]; funext q; ring
    rw [e1, qavg_lin3 hr2.le hr3.le hr4'.le]
    ring
  have hNG0 : 0 ≤ qavg S r2 r3 r4 c (fun q => if gen3 (gM m) q then 0 else 1) := by
    calc (0 : ℝ) = qavg S r2 r3 r4 c (fun _ => 0) := (qavg_const hr2.le hr3.le hr4'.le c 0).symm
      _ ≤ _ := qavg_mono' hr2.le hr3.le hr4'.le c fun _ _ _ => by split_ifs <;> norm_num
  have hX0 : (0 : ℝ) ≤ (1 / 10 ^ 6) ^ m := by positivity
  have hX1 : ((1 : ℝ) / 10 ^ 6) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hγL : L * γ ^ m ≤ (1 / 10 ^ 6) ^ m * cG / 8 := by
    have h2 : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
    calc L * γ ^ m ≤ L * (2 * (1 / 2) ^ m * (1 / 10 ^ 6) ^ m) :=
          mul_le_mul_of_nonneg_left hγm (by linarith)
      _ = (16 * L) * (1 / 2) ^ m * (1 / 10 ^ 6) ^ m / 8 := by ring
      _ ≤ (2 ^ m * cG) * (1 / 2) ^ m * (1 / 10 ^ 6) ^ m / 8 := by gcongr
      _ = (1 / 10 ^ 6) ^ m * cG / 8 := by rw [mul_comm (2 ^ m : ℝ) cG, mul_assoc cG, h2]; ring
  have hβX : β ^ m ≤ (1 / 10 ^ 6) ^ m := pow_le_pow_left₀ hβ0 hβ1 m
  have hmain : (1 / 10 ^ 6) ^ m * cG / 4 ≤ qavg S r2 r3 r4 c EW := by
    refine le_trans ?_ (qavg_mono' hr2.le hr3.le hr4'.le c hpt)
    rw [hLBq]
    exact step3_arith hX0 hX1 hcG hL hβm hβX hγL hNG0 (hNGq.trans hNG) hG
  rw [← hclaim1] at hmain
  obtain ⟨Φ, -, hΦ⟩ := exists_pos_ge hwm.1 hwm.2 _ hmain
  refine ⟨fset ξ Ω Φ, fun i => filter_subset _ _, hΦ⟩

end

end GT
end File_GT_U3S3b

open Finset KM
open scoped ComplexConjugate
open Classical
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)} {r2 r3 r4 ρh ρv A cG L : ℝ}
    (hr2 : 0 < r2) (h23 : r2 ≤ r3) (h34 : r3 ≤ r4) (hr4 : r4 ≤ 1)
    (hρh : 0 < ρh) (hρv : 0 < ρv) (h2v : 2 * ρv ≤ ρh)
    (hA0 : 0 ≤ A) (hAρ : A * ρh ≤ 1 / 1000) (hAv : A ≤ 1 / ρv) (hcG : 0 ≤ cG)
    (hL : 1 ≤ L) {m : ℕ} (hm : 1 ≤ m) (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p)
    (he : 50 * S.card * (ρv / 2) / ρh ≤ 1 / (4 * m))
    (hmL : 16 * L ≤ 2 ^ m * cG)
    (hNG : (4 * (gM m : ℝ)) ^ 3 * (1 / (p * (r2 / 4) ^ S.card)) ≤ (1 / 10 ^ 6) ^ m * cG / (8 * L))
    (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (c : Fin 4 → ZMod p)
    (hG : cG ≤ qavg S r2 r3 r4 c
      (fun q => if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0)) :
    ∃ As : Fin 4 → Finset (ZMod p), (∀ i, As i ⊆ Ω) ∧
      (1 / 10 ^ 6) ^ m * cG / 4 ≤ qavg S r2 r3 r4 c (Wt S ρv L ξ As) :=
  @GT.u3_step3 p _ hp S r2 r3 r4 ρh ρv A cG L hr2 h23 h34 hr4 hρh hρv h2v hA0 hAρ hAv hcG hL m hm hpm he hmL hNG Ω ξ c hG

