-- Prove2me | solution 1 for GT.poor_d2
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:48:51.757166+00:00
-- url     : https://prove2.me/submissions/3e922e0b-de7c-4bc0-bcaf-dbd95e59ac88

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

lemma cn_le_half (z : ZMod N) : cn z ≤ 1 / 2 := by
  have := AddCircle.norm_le_half_period (1 : ℝ) (x := ZMod.toAddCircle z) one_ne_zero
  simpa [cn] using this

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

lemma ec_add (x y : UnitAddCircle) : ec (x + y) = ec x * ec y := by
  simp [ec, AddCircle.toCircle_add]

@[simp] lemma norm_ec (x : UnitAddCircle) : ‖ec x‖ = 1 := Circle.norm_coe _

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

@[simp] lemma snorm_zero : snorm S (0 : ZMod N) = 0 := by
  unfold snorm; split_ifs <;> simp

lemma snorm_nsmul_le (n : ℕ) (h : ZMod N) : snorm S ((n : ZMod N) * h) ≤ n * snorm S h := by
  rw [snorm_le_iff (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (snorm_nonneg h))]
  intro s hs
  rw [mul_left_comm]
  exact (cn_natCast_mul_le n _).trans
    (mul_le_mul_of_nonneg_left (cn_le_snorm hs h) (Nat.cast_nonneg (α := ℝ) n))

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

lemma lq_third (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a h1 h2 h3 : ZMod p}
    (hs : snorm S (a - n0) + snorm S h1 + snorm S h2 + snorm S h3 ≤ ρ) :
    Ξ (a + h1 + h2 + h3) - Ξ (a + h1 + h2) - Ξ (a + h1 + h3) - Ξ (a + h2 + h3)
      + Ξ (a + h1) + Ξ (a + h2) + Ξ (a + h3) - Ξ a = 0 := by
  have n1 := snorm_nonneg (S := S) h1
  have n2 := snorm_nonneg (S := S) h2
  have n3 := snorm_nonneg (S := S) h3
  have n0' := snorm_nonneg (S := S) (a - n0)
  have mem : ∀ x : ZMod p, snorm S (x - n0) ≤ ρ → x ∈ sBohr S n0 ρ :=
    fun x hx => (mem_sBohr hρ).2 hx
  have t2 : ∀ u v : ZMod p, snorm S (a + u + v - n0) ≤ snorm S (a - n0) + snorm S u + snorm S v :=
    fun u v => by
      rw [show a + u + v - n0 = (a - n0) + u + v by abel]
      exact (snorm_add_le _ _).trans (add_le_add (snorm_add_le _ _) le_rfl)
  have t1 : ∀ u : ZMod p, snorm S (a + u - n0) ≤ snorm S (a - n0) + snorm S u := fun u => by
    rw [show a + u - n0 = (a - n0) + u by abel]; exact snorm_add_le _ _
  have t3 : snorm S (a + h1 + h2 + h3 - n0) ≤
      snorm S (a - n0) + snorm S h1 + snorm S h2 + snorm S h3 := by
    rw [show a + h1 + h2 + h3 - n0 = (a - n0) + h1 + h2 + h3 by abel]
    exact (snorm_add_le _ _).trans (add_le_add
      ((snorm_add_le _ _).trans (add_le_add (snorm_add_le _ _) le_rfl)) le_rfl)
  refine hL a h1 h2 h3 (mem _ (by linarith)) (mem _ (by linarith [t1 h1]))
    (mem _ (by linarith [t1 h2])) (mem _ (by linarith [t1 h3])) (mem _ (by linarith [t2 h1 h2]))
    (mem _ (by linarith [t2 h1 h3])) (mem _ (by linarith [t2 h2 h3])) (mem _ (by linarith [t3]))

/-- Base-point independence of the second difference. -/
lemma D2_base (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a t h k : ZMod p}
    (hs : snorm S (a - n0) + snorm S t + snorm S h + snorm S k ≤ ρ) :
    D2 Ξ (a + t) h k = D2 Ξ a h k := by
  have := lq_third hL hρ hs
  unfold D2
  rw [← sub_eq_zero, ← this]
  abel

/-- Additivity of the second difference in its first variable. -/
lemma D2_add_left (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a h h' k : ZMod p}
    (hs : snorm S (a - n0) + snorm S h + snorm S h' + snorm S k ≤ ρ) :
    D2 Ξ a (h + h') k = D2 Ξ a h k + D2 Ξ a h' k := by
  have e : D2 Ξ a (h + h') k = D2 Ξ a h k + D2 Ξ (a + h) h' k := by
    unfold D2; rw [← add_assoc a h h']; abel
  rw [e, D2_base hL hρ hs]

/-- Along a short progression a locally quadratic map is a quadratic polynomial. -/
lemma lq_prog (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a h : ZMod p} (j : ℕ)
    (hs : snorm S (a - n0) + j * snorm S h ≤ ρ) :
    Ξ (a + (j : ZMod p) * h) - Ξ a = j • (Ξ (a + h) - Ξ a) + (j.choose 2) • D2 Ξ a h h := by
  have hsh := snorm_nonneg (S := S) h
  -- consecutive differences
  have hstep : ∀ i : ℕ, i + 2 ≤ j →
      Ξ (a + ((i + 1 : ℕ) : ZMod p) * h) - Ξ (a + (i : ZMod p) * h) =
        (Ξ (a + h) - Ξ a) + i • D2 Ξ a h h := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hb : D2 Ξ (a + (i : ZMod p) * h) h h = D2 Ξ a h h := by
        refine D2_base hL hρ (le_trans ?_ hs)
        have : snorm S ((i : ZMod p) * h) ≤ i * snorm S h := snorm_nsmul_le i h
        have hij : (i : ℝ) + 2 ≤ j := by exact_mod_cast (by omega : i + 2 ≤ j)
        nlinarith
      have e : Ξ (a + ((i + 1 + 1 : ℕ) : ZMod p) * h) - Ξ (a + ((i + 1 : ℕ) : ZMod p) * h) =
          (Ξ (a + ((i + 1 : ℕ) : ZMod p) * h) - Ξ (a + (i : ZMod p) * h)) +
            D2 Ξ (a + (i : ZMod p) * h) h h := by
        unfold D2
        have e1 : a + ((i + 1 + 1 : ℕ) : ZMod p) * h = a + (i : ZMod p) * h + h + h := by
          push_cast; ring
        have e2 : a + ((i + 1 : ℕ) : ZMod p) * h = a + (i : ZMod p) * h + h := by push_cast; ring
        rw [e1, e2]; abel
      rw [e, ih', hb, succ_nsmul]
      abel
  induction j with
  | zero => simp
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simp
    · have hs' : snorm S (a - n0) + j * snorm S h ≤ ρ := by
        have : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
        nlinarith
      have ih' := ih hs' (fun i hi => hstep i (by omega))
      have hlast := hstep (j - 1) (by omega)
      rw [show j - 1 + 1 = j from Nat.sub_add_cancel hpos] at hlast
      have ecast : ((j - 1 : ℕ) : ZMod p) = (j : ZMod p) - 1 := by
        rw [Nat.cast_sub hpos]; simp
      have e : Ξ (a + ((j + 1 : ℕ) : ZMod p) * h) - Ξ a =
          (Ξ (a + ((j + 1 : ℕ) : ZMod p) * h) - Ξ (a + (j : ZMod p) * h)) +
          (Ξ (a + (j : ZMod p) * h) - Ξ a) := by abel
      have hnext := hstep j
      -- use the step from `j` to `j + 1` via the step from `j - 1` to `j`
      have hb : D2 Ξ (a + ((j - 1 : ℕ) : ZMod p) * h) h h = D2 Ξ a h h := by
        refine D2_base hL hρ (le_trans ?_ hs)
        have : snorm S (((j - 1 : ℕ) : ZMod p) * h) ≤ (j - 1 : ℕ) * snorm S h :=
          snorm_nsmul_le _ h
        have hij : ((j - 1 : ℕ) : ℝ) + 2 ≤ (j + 1 : ℕ) := by
          push_cast [Nat.cast_sub hpos]; linarith
        nlinarith
      have estep : Ξ (a + ((j + 1 : ℕ) : ZMod p) * h) - Ξ (a + (j : ZMod p) * h) =
          (Ξ (a + (j : ZMod p) * h) - Ξ (a + ((j - 1 : ℕ) : ZMod p) * h)) +
            D2 Ξ (a + ((j - 1 : ℕ) : ZMod p) * h) h h := by
        unfold D2
        have e1 : a + ((j + 1 : ℕ) : ZMod p) * h = a + ((j - 1 : ℕ) : ZMod p) * h + h + h := by
          rw [ecast]; push_cast; ring
        have e2 : a + (j : ZMod p) * h = a + ((j - 1 : ℕ) : ZMod p) * h + h := by
          rw [ecast]; ring
        rw [e1, e2]; abel
      have hc : (j + 1).choose 2 = j.choose 2 + j := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      have hj : (j - 1) • D2 Ξ a h h + D2 Ξ a h h = j • D2 Ξ a h h := by
        rw [← succ_nsmul, Nat.sub_add_cancel hpos]
      rw [e, estep, hlast, hb, ih', hc, add_nsmul, succ_nsmul,
        add_assoc (Ξ (a + h) - Ξ a), hj]
      generalize Ξ (a + h) - Ξ a = Δ
      generalize D2 Ξ a h h = D
      rw [add_nsmul]
      abel

end

end GT
end File_GT_LocQ

section File_GT_LargeQuad
/-!
# Large local quadratic exponential sums (Green–Tao, Proposition 4.9)
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- Shifting both arguments of a double average against regular Bohr distributions. -/
lemma shift2 {Γ : Finset (ZMod p)} {ρ1 ρ τ : ℝ} (hρ1 : 0 < ρ1) (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (h41 : 4 * τ ≤ ρ1) (h4 : 4 * τ ≤ ρ)
    {h h' : ZMod p} (hh : snorm Γ h ≤ τ) (hh' : snorm Γ h' ≤ τ) (F : ZMod p → ZMod p → ℂ)
    (hF : ∀ x y, ‖F x y‖ ≤ 1) :
    ‖∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F (x + h) (y + h') -
      ∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F x y‖ ≤ 50 * Γ.card * τ / ρ1 + 50 * Γ.card * τ / ρ := by
  have hD := regP_isDist Γ hρ.le
  have hD1 := regP_isDist Γ hρ1.le
  have hmem : h ∈ bohr Γ τ := (mem_bohr_iff_snorm hτ).2 hh
  have hmem' : h' ∈ bohr Γ τ := (mem_bohr_iff_snorm hτ).2 hh'
  have e1 : ∀ G : ZMod p → ZMod p → ℂ, ∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * G x y =
      ∑ y, (regP Γ ρ y : ℂ) * ∑ x, (regP Γ ρ1 x : ℂ) * G x y := by
    intro G; rw [sum_comm]; refine sum_congr rfl fun y _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
  have e2 : ∀ G : ZMod p → ZMod p → ℂ, ∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * G x y =
      ∑ x, (regP Γ ρ1 x : ℂ) * ∑ y, (regP Γ ρ y : ℂ) * G x y := by
    intro G; refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  have hA : ‖∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F (x + h) (y + h') -
      ∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F x (y + h')‖ ≤ 50 * Γ.card * τ / ρ1 := by
    rw [e1 (fun x y => F (x + h) (y + h')), e1 (fun x y => F x (y + h')), ← sum_sub_distrib]
    have : ∀ y, (regP Γ ρ y : ℂ) * (∑ x, (regP Γ ρ1 x : ℂ) * F (x + h) (y + h')) -
        (regP Γ ρ y : ℂ) * ∑ x, (regP Γ ρ1 x : ℂ) * F x (y + h') =
        (regP Γ ρ y : ℂ) * ((∑ x, (regP Γ ρ1 x : ℂ) * F (x + h) (y + h')) -
          ∑ x, (regP Γ ρ1 x : ℂ) * F x (y + h')) := fun y => by ring
    simp only [this]
    refine norm_wavg_le hD.1 hD.2 _ fun y _ => ?_
    have := regP_shift (Γ := Γ) (Γ' := Γ) subset_rfl hρ1 hτ h41 hmem (B := 1)
      (fun x => F x (y + h')) (fun x => hF _ _)
    simpa using this
  have hB : ‖∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F x (y + h') -
      ∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F x y‖ ≤ 50 * Γ.card * τ / ρ := by
    rw [e2 (fun x y => F x (y + h')), e2 F, ← sum_sub_distrib]
    have : ∀ x, (regP Γ ρ1 x : ℂ) * (∑ y, (regP Γ ρ y : ℂ) * F x (y + h')) -
        (regP Γ ρ1 x : ℂ) * ∑ y, (regP Γ ρ y : ℂ) * F x y =
        (regP Γ ρ1 x : ℂ) * ((∑ y, (regP Γ ρ y : ℂ) * F x (y + h')) -
          ∑ y, (regP Γ ρ y : ℂ) * F x y) := fun x => by ring
    simp only [this]
    refine norm_wavg_le hD1.1 hD1.2 _ fun x _ => ?_
    have := regP_shift (Γ := Γ) (Γ' := Γ) subset_rfl hρ hτ h4 hmem' (B := 1)
      (fun y => F x y) (fun y => hF _ _)
    simpa using this
  have := norm_sub_le_norm_sub_add_norm_sub
    (∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F (x + h) (y + h'))
    (∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F x (y + h'))
    (∑ x, ∑ y, (regP Γ ρ1 x : ℂ) * (regP Γ ρ y : ℂ) * F x y)
  linarith

end

end GT
end File_GT_LargeQuad

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

/-- Shifting both variables of an average against `P_{ρ/2}(a - n₀) ⊗ P_{ρ_r}(r)`. -/
lemma shiftAR {S : Finset (ZMod p)} {n0 : ZMod p} {ρ ρr τ : ℝ} (hρ : 0 < ρ) (hρr : 0 < ρr)
    (hτ : 0 ≤ τ) (h4 : 4 * τ ≤ ρ / 2) (h4r : 4 * τ ≤ ρr) {t u : ZMod p}
    (ht : snorm S t ≤ τ) (hu : snorm S u ≤ τ) (f : ZMod p → ZMod p → ℂ)
    (hf : ∀ a r, ‖f a r‖ ≤ 1) :
    ‖∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) * f (a + t) (r + u) -
      ∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) * f a r‖ ≤
      50 * S.card * τ / (ρ / 2) + 50 * S.card * τ / ρr := by
  have e : ∀ g : ZMod p → ZMod p → ℂ, ∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
      (regP S ρr r : ℂ) * g a r = ∑ x, ∑ r, (regP S (ρ / 2) x : ℂ) * (regP S ρr r : ℂ) *
        g (x + n0) r := by
    intro g
    exact sum_regP_shift_center (S := S) (ρ := ρ / 2) n0
      (fun a w => ∑ r, (w : ℂ) * (regP S ρr r : ℂ) * g a r)
  rw [e (fun a r => f (a + t) (r + u)), e f]
  have := shift2 (Γ := S) (by positivity : (0 : ℝ) < ρ / 2) hρr hτ h4 h4r ht hu
    (fun x r => f (x + n0) r) (fun x r => hf _ _)
  (try simp only at this)
  have e2 : ∀ x r, f (x + n0 + t) (r + u) = f (x + t + n0) (r + u) := fun x r => by
    rw [add_right_comm]
  simp only [e2]
  exact this

/-- Restricting a double sum to the supports of the weights. -/
lemma sum2_congr_supp {P Q : ZMod p → ℝ} {F F' : ZMod p → ZMod p → ℂ}
    (h : ∀ r s, P r ≠ 0 → Q s ≠ 0 → F r s = F' r s) :
    ∑ r, ∑ s, (P r : ℂ) * (Q s : ℂ) * F r s = ∑ r, ∑ s, (P r : ℂ) * (Q s : ℂ) * F' r s := by
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  by_cases hr : P r = 0
  · simp [hr]
  by_cases hs : Q s = 0
  · simp [hs]
  rw [h r s hr hs]

lemma sum_regP_center (S : Finset (ZMod p)) {ρ : ℝ} (hρ : 0 ≤ ρ) (n0 : ZMod p) :
    ∑ a, regP S ρ (a - n0) = 1 := by
  rw [sum_regP_shift_center (S := S) (ρ := ρ) n0 (fun _ w => w)]
  exact sum_regP S hρ

set_option maxHeartbeats 2000000 in
/-- Shift, average and pigeonhole: the common core of the heads of Weyl differencing. -/
lemma wd_shift_pigeon {S : Finset (ZMod p)} {n0 : ZMod p} {ρ ρr ρh δ : ℝ} (hρ : 0 < ρ)
    (hρr : 0 < ρr) (hρh : 0 < ρh) (h4 : 4 * ρh ≤ ρ / 2) (h4r : 4 * ρh ≤ ρr)
    (hsep : 50 * S.card * ρh / (ρ / 2) + 50 * S.card * ρh / ρr ≤ δ / 2)
    (f : ZMod p → ZMod p → ℂ) (hf : ∀ a r, ‖f a r‖ ≤ 1) (ts us : ZMod p → ZMod p)
    (hts : ∀ h, snorm S h ≤ ρh → snorm S (ts h) ≤ ρh)
    (hus : ∀ h, snorm S h ≤ ρh → snorm S (us h) ≤ ρh)
    (h : δ ≤ ‖∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) * f a r‖) :
    ∃ a0, regP S (ρ / 2) (a0 - n0) ≠ 0 ∧ δ / 2 ≤
      ‖∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) * f (a0 + ts h) (r + us h)‖ := by
  have hDh := regP_isDist S hρh.le
  obtain ⟨V, hV⟩ : ∃ V : ℂ, V = ∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
      (regP S ρr r : ℂ) * f a r := ⟨_, rfl⟩
  rw [← hV] at h
  have hW : ‖∑ h, (regP S ρh h : ℂ) * (∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
      (regP S ρr r : ℂ) * f (a + ts h) (r + us h)) - V‖ ≤ δ / 2 := by
    refine norm_wavg_sub_le hDh.1 hDh.2 _ V fun hh hne => ?_
    have hsh : snorm S hh ≤ ρh :=
      snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρh.le hne) hρh.le
    rw [hV]
    exact (shiftAR hρ hρr hρh.le h4 h4r (hts hh hsh) (hus hh hsh) f hf).trans hsep
  have hW' : δ / 2 ≤ ‖∑ h, (regP S ρh h : ℂ) * (∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
      (regP S ρr r : ℂ) * f (a + ts h) (r + us h))‖ := by
    have := norm_sub_norm_le V (∑ h, (regP S ρh h : ℂ) * (∑ a, ∑ r,
      (regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) * f (a + ts h) (r + us h)))
    rw [norm_sub_rev] at this
    linarith
  have hre : ∑ h, (regP S ρh h : ℂ) * (∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
      (regP S ρr r : ℂ) * f (a + ts h) (r + us h)) = ∑ a, (regP S (ρ / 2) (a - n0) : ℂ) *
      ∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) * f (a + ts h) (r + us h) := by
    obtain ⟨G, hG⟩ : ∃ G : ZMod p → ZMod p → ZMod p → ℂ, ∀ h a r, G h a r =
        (regP S ρh h : ℂ) * ((regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) *
          f (a + ts h) (r + us h)) := ⟨_, fun _ _ _ => rfl⟩
    have l : ∑ h, (regP S ρh h : ℂ) * (∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
        (regP S ρr r : ℂ) * f (a + ts h) (r + us h)) = ∑ h, ∑ a, ∑ r, G h a r := by
      refine sum_congr rfl fun h _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun r _ => ?_
      rw [hG]
    have r' : ∑ a, (regP S (ρ / 2) (a - n0) : ℂ) * ∑ r, ∑ h, (regP S ρr r : ℂ) *
        (regP S ρh h : ℂ) * f (a + ts h) (r + us h) = ∑ a, ∑ r, ∑ h, G h a r := by
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun h _ => ?_
      rw [hG]; ring
    rw [l, r']
    calc ∑ h, ∑ a, ∑ r, G h a r = ∑ a, ∑ h, ∑ r, G h a r := sum_comm
      _ = ∑ a, ∑ r, ∑ h, G h a r := sum_congr rfl fun a _ => sum_comm
  rw [hre] at hW'
  have hA : ∀ a, 0 ≤ regP S (ρ / 2) (a - n0) := fun a => regP_nonneg S _
  have hA1 : ∑ a, regP S (ρ / 2) (a - n0) = 1 := sum_regP_center S (by positivity) n0
  have h3 : δ / 2 ≤ ∑ a, regP S (ρ / 2) (a - n0) * ‖∑ r, ∑ h, (regP S ρr r : ℂ) *
      (regP S ρh h : ℂ) * f (a + ts h) (r + us h)‖ := by
    refine hW'.trans ((norm_sum_le _ _).trans (sum_le_sum fun a _ => le_of_eq ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA a)]
  obtain ⟨a0, ha0, h4'⟩ := exists_pos_ge hA hA1 _ h3
  exact ⟨a0, ha0, h4'⟩

set_option maxHeartbeats 2000000 in
/-- Head of Weyl differencing, case `k₂ = 0`: phase `ψ₀(a) + ψ₁(a + r)`. -/
theorem wd_head1 {S : Finset (ZMod p)} {n0 : ZMod p} {ρ ρr ρh δ : ℝ} (hρ : 0 < ρ)
    (hρr : 0 < ρr) (hρh : 0 < ρh) (h4 : 4 * ρh ≤ ρ / 2) (h4r : 4 * ρh ≤ ρr)
    (hsep : 50 * S.card * ρh / (ρ / 2) + 50 * S.card * ρh / ρr ≤ δ / 2)
    (ψ0 ψ1 : ZMod p → UnitAddCircle)
    (h : δ ≤ ‖∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) *
      ec (ψ0 a + ψ1 (a + r))‖) :
    ∃ a0, snorm S (a0 - n0) ≤ ρ / 2 ∧ ∃ b1 b2 : ZMod p → ℂ, (∀ r, ‖b1 r‖ ≤ 1) ∧
      (∀ h, ‖b2 h‖ ≤ 1) ∧ δ / 2 ≤ ‖∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
        (b1 r * b2 h * ec (D2 ψ1 a0 r h))‖ := by
  obtain ⟨a0, ha0, hbig⟩ := wd_shift_pigeon hρ hρr hρh h4 h4r hsep
    (fun a r => ec (ψ0 a + ψ1 (a + r))) (fun a r => by simp) (fun h => h) (fun _ => 0)
    (fun h hh => hh) (fun h _ => by simp; linarith) h
  refine ⟨a0, snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) ha0) (by positivity),
    fun r => ec (ψ1 (a0 + r) - ψ1 a0), fun h => ec (ψ0 (a0 + h) + ψ1 (a0 + h)),
    fun r => by simp, fun h => by simp, hbig.trans (le_of_eq ?_)⟩
  congr 1
  refine sum_congr rfl fun r _ => sum_congr rfl fun h _ => ?_
  simp only [add_zero]
  rw [← ec_add, ← ec_add]
  congr 2
  unfold D2
  rw [show a0 + h + r = a0 + r + h by abel]
  abel

set_option maxHeartbeats 2000000 in
/-- Head of Weyl differencing, general case: phase `ψ₀(a) + ψ₁(a+r) + ψ₂(a+2r)`, giving the
second difference of `2ψ₂`. -/
theorem wd_head2 {S : Finset (ZMod p)} {n0 : ZMod p} {ρ ρr ρh δ : ℝ} (hρ : 0 < ρ)
    (hρr : 0 < ρr) (hρh : 0 < ρh) (h4 : 4 * ρh ≤ ρ / 2) (h4r : 4 * ρh ≤ ρr)
    (hbud : 2 * ρr + ρh ≤ ρ / 2)
    (hsep : 50 * S.card * ρh / (ρ / 2) + 50 * S.card * ρh / ρr ≤ δ / 2)
    (ψ0 ψ1 ψ2 : ZMod p → UnitAddCircle) (hL : LocQuad (sBohr S n0 ρ) ψ2)
    (h : δ ≤ ‖∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) *
      ec (ψ0 a + ψ1 (a + r) + ψ2 (a + 2 * r))‖) :
    ∃ a0, snorm S (a0 - n0) ≤ ρ / 2 ∧ ∃ b1 b2 : ZMod p → ℂ, (∀ r, ‖b1 r‖ ≤ 1) ∧
      (∀ h, ‖b2 h‖ ≤ 1) ∧ δ / 2 ≤ ‖∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
        (b1 r * b2 h * ec (D2 (fun x => 2 • ψ2 x) a0 r h))‖ := by
  obtain ⟨a0, ha0, hbig⟩ := wd_shift_pigeon hρ hρr hρh h4 h4r hsep
    (fun a r => ec (ψ0 a + ψ1 (a + r) + ψ2 (a + 2 * r))) (fun a r => by simp) (fun h => -h)
    (fun h => h) (fun h hh => by rw [snorm_neg]; exact hh) (fun h hh => hh) h
  have hsa : snorm S (a0 - n0) ≤ ρ / 2 :=
    snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) ha0) (by positivity)
  refine ⟨a0, hsa, fun r => ec (ψ1 (a0 + r) + ψ2 (a0 + 2 * r) - ψ2 a0),
    fun h => ec (ψ0 (a0 + -h) + ψ2 (a0 + h)), fun r => by simp, fun h => by simp,
    hbig.trans (le_of_eq ?_)⟩
  congr 1
  refine sum2_congr_supp fun r h hr hh => ?_
  have hsr : snorm S r ≤ ρr := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρr.le hr) hρr.le
  have hsh : snorm S h ≤ ρh := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρh.le hh) hρh.le
  have hD : D2 (fun x => 2 • ψ2 x) a0 r h = D2 ψ2 a0 (2 * r) h := by
    have e1 : D2 (fun x => 2 • ψ2 x) a0 r h = 2 • D2 ψ2 a0 r h := by
      unfold D2; simp only [nsmul_sub, nsmul_add]
    rw [e1, two_mul, D2_add_left hL hρ.le (by linarith), two_nsmul]
  rw [hD, ← ec_add, ← ec_add]
  congr 1
  unfold D2
  rw [show a0 + -h + (r + h) = a0 + r by abel,
    show a0 + -h + 2 * (r + h) = a0 + 2 * r + h by ring]
  abel

end

end GT
end File_GT_WD

section File_GT_WeylStep
/-!
# The Weyl step of Proposition 7.1 (Green–Tao, Lemmas 3.2 and 7.2)

A poorly distributed label produces a non-zero frequency `k = (k₀, k₁, k₂)` with coordinates
`|k_{j,i}| ≲ (d/η)‖v_i‖` such that `E e(k₀·Ξ(a) + k₁·Ξ(a+r) + k₂·Ξ(a+2r))` is large.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

lemma kdot_apply {ι : Type*} [Fintype ι] (k : ι → ℤ) (x : ι → UnitAddCircle) :
    kdot k x = ∑ i, k i • x i := rfl

/-- The Cauchy–Schwarz inequality behind Lemma 3.2, on a finite abelian group. -/
lemma grid_cauchy {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] (f : Γ → ℝ) :
    (∑ x, f x) ^ 4 ≤ Fintype.card Γ *
      ∑ x, ∑ y, ∑ z, f x * f y * f z * f (x - 3 • y + 3 • z) := by
  set g : Γ → ℝ := fun w => ∑ y, f (w + 3 • y) * f y with hg
  have e1 : ∑ x, ∑ y, ∑ z, f x * f y * f z * f (x - 3 • y + 3 • z) = ∑ w, g w ^ 2 := by
    rw [sum_comm]
    have : ∀ y, ∑ x, ∑ z, f x * f y * f z * f (x - 3 • y + 3 • z) =
        ∑ w, ∑ z, f (w + 3 • y) * f y * f z * f (w + 3 • z) := by
      intro y
      refine (Fintype.sum_equiv (Equiv.subRight (3 • y)) _ _ fun x => ?_)
      simp only [Equiv.subRight_apply, sub_add_cancel]
    rw [sum_congr rfl fun y _ => this y, sum_comm]
    refine sum_congr rfl fun w _ => ?_
    rw [hg, sq, sum_mul_sum]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    ring
  have e2 : ∑ w, g w = (∑ x, f x) ^ 2 := by
    rw [hg, sum_comm, sq, sum_mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_mul]
    have : ∑ w, f (w + 3 • y) = ∑ x, f x :=
      Fintype.sum_equiv (Equiv.addRight (3 • y)) _ _ fun x => rfl
    rw [this, sum_mul]
    exact sum_congr rfl fun _ _ => mul_comm _ _
  have := sq_sum_le_card_mul_sum_sq (s := univ) (f := g)
  rw [e1]
  rw [e2, card_univ] at this
  nlinarith [this]

namespace DTorus

lemma norm_emb_le (G : DTorus) (t : Fin G.d → ℝ) : ‖G.emb t‖ ≤ ∑ i, ‖G.v i‖ * |t i| := by
  unfold emb
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
  rw [norm_smul, Real.norm_eq_abs, mul_comm]

lemma IsLip.coord {G : DTorus} {F : G.Pt → ℝ} (hF : G.IsLip F) (t t' : Fin G.d → ℝ) :
    |F (G.pt t) - F (G.pt t')| ≤ ∑ i, ‖G.v i‖ * |t i - t' i| :=
  (hF t t').trans ((G.norm_emb_le _).trans (le_of_eq (by simp [Pi.sub_apply])))

lemma Good.one_le_norm {G : DTorus} (hG : G.Good) (i : Fin G.d) : 1 ≤ ‖G.v i‖ := by
  classical
  have h := hG.2.1 (Pi.single i 1 : Fin G.d → ℤ) (by simp)
  have e : G.emb (fun j => (((Pi.single i 1 : Fin G.d → ℤ) j : ℤ) : ℝ)) = G.v i := by
    unfold emb
    rw [sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rwa [e] at h

end DTorus

/-- `|abcd - a'b'c'd'| ≤ |a-a'| + |b-b'| + |c-c'| + |d-d'|` for `1`-bounded reals. -/
lemma abs_prod4_sub_le {a b c d a' b' c' d' : ℝ} (hb : |b| ≤ 1) (hc : |c| ≤ 1)
    (hd : |d| ≤ 1) (ha' : |a'| ≤ 1) (hb' : |b'| ≤ 1) (hc' : |c'| ≤ 1) :
    |a * b * c * d - a' * b' * c' * d'| ≤ |a - a'| + |b - b'| + |c - c'| + |d - d'| := by
  have e : a * b * c * d - a' * b' * c' * d' = (a - a') * (b * c * d) + a' * (b - b') * (c * d) +
      a' * b' * (c - c') * d + a' * b' * c' * (d - d') := by ring
  rw [e]
  have h1 : |(a - a') * (b * c * d)| ≤ |a - a'| := by
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_mul, abs_mul]
    exact mul_le_one₀ (mul_le_one₀ hb (abs_nonneg _) hc) (abs_nonneg _) hd
  have h2 : |a' * (b - b') * (c * d)| ≤ |b - b'| := by
    rw [abs_mul, abs_mul, abs_mul]
    have := mul_le_one₀ hc (abs_nonneg _) hd
    calc |a'| * |b - b'| * (|c| * |d|) ≤ 1 * |b - b'| * 1 := by gcongr
      _ = _ := by ring
  have h3 : |a' * b' * (c - c') * d| ≤ |c - c'| := by
    rw [abs_mul, abs_mul, abs_mul]
    calc |a'| * |b'| * |c - c'| * |d| ≤ 1 * 1 * |c - c'| * 1 := by gcongr
      _ = _ := by ring
  have h4 : |a' * b' * c' * (d - d')| ≤ |d - d'| := by
    rw [abs_mul, abs_mul, abs_mul]
    calc |a'| * |b'| * |c'| * |d - d'| ≤ 1 * 1 * 1 * |d - d'| := by gcongr
      _ = _ := by ring
  calc _ ≤ |(a - a') * (b * c * d)| + |a' * (b - b') * (c * d)| + |a' * b' * (c - c') * d| +
        |a' * b' * c' * (d - d')| := by
          refine (abs_add_le _ _).trans ?_
          refine add_le_add_left ((abs_add_le _ _).trans ?_) _
          exact add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by linarith

/-- Three copies of the coordinates of a torus. -/
abbrev K3 (d : ℕ) : Type := Fin d ⊕ (Fin d ⊕ Fin d)

/-- Packing three points of `(ℝ/ℤ)^d` into one point of `(ℝ/ℤ)^{3d}`. -/
def pack3 {α : Type*} {d : ℕ} (x0 x1 x2 : Fin d → α) : K3 d → α :=
  Sum.elim x0 (Sum.elim x1 x2)

lemma sum_K3 {d : ℕ} {M : Type*} [AddCommMonoid M] (f : K3 d → M) :
    ∑ k, f k = (∑ i, f (.inl i)) + ((∑ i, f (.inr (.inl i))) + ∑ i, f (.inr (.inr i))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]

lemma prod_K3 {d : ℕ} {M : Type*} [CommMonoid M] (f : K3 d → M) :
    ∏ k, f k = (∏ i, f (.inl i)) * ((∏ i, f (.inr (.inl i))) * ∏ i, f (.inr (.inr i))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]

lemma sum_fun_K3 {d N : ℕ} {M : Type*} [AddCommMonoid M]
    (H : (Fin d → ZMod N) → (Fin d → ZMod N) → (Fin d → ZMod N) → M) [NeZero N] :
    ∑ g : K3 d → ZMod N, H (fun i => g (.inl i)) (fun i => g (.inr (.inl i)))
      (fun i => g (.inr (.inr i))) = ∑ x, ∑ y, ∑ z, H x y z := by
  rw [← (Equiv.sumArrowEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← (Equiv.sumArrowEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- The coordinate index of `K3 d`. -/
def kidx {d : ℕ} : K3 d → Fin d := Sum.elim id (Sum.elim id id)

/-- `F^{(1)}(x_0, x_1, x_2) = F(x_0)`. -/
def F1 (G : DTorus) (F : G.Pt → ℝ) (X : K3 G.d → UnitAddCircle) : ℝ := F (fun i => X (.inl i))

/-- `F^{(3)}(x_0, x_1, x_2) = F(x_0) F(x_1) F(x_2) F(x_0 - 3x_1 + 3x_2)`. -/
def F3 (G : DTorus) (F : G.Pt → ℝ) (X : K3 G.d → UnitAddCircle) : ℝ :=
  F (fun i => X (.inl i)) * F (fun i => X (.inr (.inl i))) * F (fun i => X (.inr (.inr i))) *
    F (fun i => X (.inl i) - 3 • X (.inr (.inl i)) + 3 • X (.inr (.inr i)))

lemma coe_lin3 (a b c : ℝ) : ((a - 3 * b + 3 * c : ℝ) : UnitAddCircle) =
    (a : UnitAddCircle) - 3 • (b : UnitAddCircle) + 3 • (c : UnitAddCircle) := by
  rw [AddCircle.coe_add, AddCircle.coe_sub, ← AddCircle.coe_nsmul, ← AddCircle.coe_nsmul]
  simp [nsmul_eq_mul]

lemma clip_F1 {G : DTorus} {F : G.Pt → ℝ} (hF : G.IsLip F) :
    CLip (fun k => 4 * ‖G.v (kidx k)‖) (F1 G F) := by
  intro t t'
  have h := hF.coord (fun i => t (.inl i)) (fun i => t' (.inl i))
  refine h.trans ?_
  rw [sum_K3]
  simp only [kidx, Sum.elim_inl, Sum.elim_inr, id]
  have h1 : ∑ i, ‖G.v i‖ * |t (.inl i) - t' (.inl i)| ≤
      ∑ i, 4 * ‖G.v i‖ * |t (.inl i) - t' (.inl i)| :=
    sum_le_sum fun i _ => by nlinarith [norm_nonneg (G.v i), abs_nonneg (t (.inl i) - t' (.inl i))]
  have h2 : 0 ≤ ∑ i, 4 * ‖G.v i‖ * |t (.inr (.inl i)) - t' (.inr (.inl i))| :=
    sum_nonneg fun i _ => by positivity
  have h3 : 0 ≤ ∑ i, 4 * ‖G.v i‖ * |t (.inr (.inr i)) - t' (.inr (.inr i))| :=
    sum_nonneg fun i _ => by positivity
  linarith

lemma clip_F3 {G : DTorus} {F : G.Pt → ℝ} (hF : G.IsLip F) (hF1 : ∀ x, |F x| ≤ 1) :
    CLip (fun k => 4 * ‖G.v (kidx k)‖) (F3 G F) := by
  intro t t'
  set s0 : Fin G.d → ℝ := fun i => t (.inl i)
  set s1 : Fin G.d → ℝ := fun i => t (.inr (.inl i))
  set s2 : Fin G.d → ℝ := fun i => t (.inr (.inr i))
  set s0' : Fin G.d → ℝ := fun i => t' (.inl i)
  set s1' : Fin G.d → ℝ := fun i => t' (.inr (.inl i))
  set s2' : Fin G.d → ℝ := fun i => t' (.inr (.inr i))
  have e : ∀ u : K3 G.d → ℝ, (fun i => ((u (.inl i) : ℝ) : UnitAddCircle) -
      3 • ((u (.inr (.inl i)) : ℝ) : UnitAddCircle) + 3 • ((u (.inr (.inr i)) : ℝ) : UnitAddCircle))
      = G.pt (fun i => u (.inl i) - 3 * u (.inr (.inl i)) + 3 * u (.inr (.inr i))) := by
    intro u; funext i; simp only [DTorus.pt]; rw [coe_lin3]
  unfold F3
  try simp only
  rw [e t, e t']
  have hab := abs_prod4_sub_le (a := F (G.pt s0)) (hF1 (G.pt s1)) (hF1 (G.pt s2))
    (hF1 (G.pt fun i => t (.inl i) - 3 * t (.inr (.inl i)) + 3 * t (.inr (.inr i))))
    (hF1 (G.pt s0')) (hF1 (G.pt s1')) (hF1 (G.pt s2'))
    (d' := F (G.pt fun i => t' (.inl i) - 3 * t' (.inr (.inl i)) + 3 * t' (.inr (.inr i))))
  refine hab.trans ?_
  have h0 := hF.coord s0 s0'
  have h1 := hF.coord s1 s1'
  have h2 := hF.coord s2 s2'
  have h3 := hF.coord (fun i => t (.inl i) - 3 * t (.inr (.inl i)) + 3 * t (.inr (.inr i)))
    (fun i => t' (.inl i) - 3 * t' (.inr (.inl i)) + 3 * t' (.inr (.inr i)))
  have h3' : ∑ i, ‖G.v i‖ * |(t (.inl i) - 3 * t (.inr (.inl i)) + 3 * t (.inr (.inr i))) -
      (t' (.inl i) - 3 * t' (.inr (.inl i)) + 3 * t' (.inr (.inr i)))| ≤
      ∑ i, ‖G.v i‖ * (|s0 i - s0' i| + 3 * |s1 i - s1' i| + 3 * |s2 i - s2' i|) := by
    refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have e2 : (t (.inl i) - 3 * t (.inr (.inl i)) + 3 * t (.inr (.inr i))) -
        (t' (.inl i) - 3 * t' (.inr (.inl i)) + 3 * t' (.inr (.inr i))) =
        (s0 i - s0' i) + (-3) * (s1 i - s1' i) + 3 * (s2 i - s2' i) := by
      simp only [s0, s1, s2, s0', s1', s2']; ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans ?_) ?_
    · rw [abs_mul]; norm_num
    · rw [abs_mul]; norm_num
  rw [sum_K3]
  simp only [kidx, Sum.elim_inl, Sum.elim_inr, id]
  have key : ∑ i, ‖G.v i‖ * |s0 i - s0' i| + ∑ i, ‖G.v i‖ * |s1 i - s1' i| +
      ∑ i, ‖G.v i‖ * |s2 i - s2' i| +
      ∑ i, ‖G.v i‖ * (|s0 i - s0' i| + 3 * |s1 i - s1' i| + 3 * |s2 i - s2' i|) ≤
      ∑ i, 4 * ‖G.v i‖ * |s0 i - s0' i| + (∑ i, 4 * ‖G.v i‖ * |s1 i - s1' i| +
        ∑ i, 4 * ‖G.v i‖ * |s2 i - s2' i|) := by
    simp only [← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    have := norm_nonneg (G.v i)
    have := abs_nonneg (s0 i - s0' i)
    nlinarith [abs_nonneg (s1 i - s1' i), abs_nonneg (s2 i - s2' i)]
  have := add_le_add (add_le_add (add_le_add h0 h1) h2) (h3.trans h3')
  exact this.trans key

lemma grid_mean_ineq {G : DTorus} (F : G.Pt → ℝ) (N : ℕ) [NeZero N] :
    ((∑ g : K3 G.d → ZMod N, F1 G F (gridPt g)) / ((N : ℝ) ^ G.d) ^ 3) ^ 4 ≤
      (∑ g : K3 G.d → ZMod N, F3 G F (gridPt g)) / ((N : ℝ) ^ G.d) ^ 3 := by
  set f : (Fin G.d → ZMod N) → ℝ := fun x => F (gridPt x) with hf
  have e1 : ∑ g : K3 G.d → ZMod N, F1 G F (gridPt g) = ((N : ℝ) ^ G.d) ^ 2 * ∑ x, f x := by
    have := sum_fun_K3 (N := N) (d := G.d) (fun x _ _ => f x)
    try simp only at this
    unfold F1
    rw [show (∑ g : K3 G.d → ZMod N, F (fun i => gridPt g (Sum.inl i))) =
      ∑ g : K3 G.d → ZMod N, f (fun i => g (Sum.inl i)) from rfl, this, Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [sum_const, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have e3 : ∑ g : K3 G.d → ZMod N, F3 G F (gridPt g) =
      ∑ x, ∑ y, ∑ z, f x * f y * f z * f (x - 3 • y + 3 • z) := by
    rw [← sum_fun_K3 (N := N) (d := G.d) (fun x y z => f x * f y * f z * f (x - 3 • y + 3 • z))]
    refine sum_congr rfl fun g _ => ?_
    unfold F3
    simp only [hf]
    congr 2
    funext i
    simp only [gridPt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, map_add, map_sub, map_nsmul]
  have hc := grid_cauchy f
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hc
  rw [e1, e3]
  have hn : (0 : ℝ) < (N : ℝ) ^ G.d := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  set n : ℝ := (N : ℝ) ^ G.d
  push_cast at hc
  rw [show (n ^ 2 * ∑ x, f x) / n ^ 3 = (∑ x, f x) / n by field_simp]
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∑ x, f x) ^ 4 * n ^ 3 ≤
        (n * ∑ x, ∑ y, ∑ z, f x * f y * f z * f (x - 3 • y + 3 • z)) * n ^ 3 :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

lemma abs_pow_four_sub_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a ^ 4 - b ^ 4| ≤ 4 * |a - b| := by
  have e : a ^ 4 - b ^ 4 = (a - b) * ((a + b) * (a ^ 2 + b ^ 2)) := by ring
  rw [e, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_mul]
  have h1 : |a + b| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have h2 : |a ^ 2 + b ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have : a ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg a]
    have : b ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg b]
    linarith
  calc |a + b| * |a ^ 2 + b ^ 2| ≤ 2 * 2 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 4 := by norm_num

lemma card_K3_fun (d N : ℕ) [NeZero N] :
    (Fintype.card (K3 d → ZMod N) : ℝ) = ((N : ℝ) ^ d) ^ 3 := by
  rw [Fintype.card_fun, Fintype.card_sum, Fintype.card_sum, ZMod.card, Fintype.card_fin]
  push_cast; ring

set_option maxHeartbeats 2000000 in
/-- **Lemma 7.2** (Weyl equidistribution, grid version): a poorly distributed configuration of a
Lipschitz function along the quadratic progression `x₀, x₁, x₂, x₀ - 3x₁ + 3x₂` correlates with
a non-trivial character `e(k₀·x₀ + k₁·x₁ + k₂·x₂)` with `|k_{j,i}| < 2 M_i`. -/
theorem weyl_step {G : DTorus} (hG : G.Good) {F : G.Pt → ℝ} (hF : G.IsLip F)
    (hF1 : ∀ x, |F x| ≤ 1) {ι : Type*} [Fintype ι] (ω : ι → ℝ) (hω0 : ∀ j, 0 ≤ ω j)
    (hω1 : ∑ j, ω j = 1) (x0 x1 x2 x3 : ι → G.Pt)
    (hx3 : ∀ j, ω j ≠ 0 → x3 j = x0 j - 3 • x1 j + 3 • x2 j) {η : ℝ} (hη : 0 < η)
    (hpoor : ∑ j, ω j * (F (x0 j) * F (x1 j) * F (x2 j) * F (x3 j)) <
      (∑ j, ω j * F (x0 j)) ^ 4 - η / 2) :
    ∃ k0 k1 k2 : Fin G.d → ℤ, (k0 ≠ 0 ∨ k1 ≠ 0 ∨ k2 ≠ 0) ∧
      (∀ i, |k0 i| < 2 * wM G η i ∧ |k1 i| < 2 * wM G η i ∧ |k2 i| < 2 * wM G η i) ∧
      η / (256 * (∏ i, (2 * wM G η i : ℝ)) ^ 3) ≤
        ‖∑ j, (ω j : ℂ) * ec (kdot k0 (x0 j) + kdot k1 (x1 j) + kdot k2 (x2 j))‖ := by
  classical
  set M : K3 G.d → ℕ := fun k => wM G η (kidx k) with hMdef
  set w : K3 G.d → ℝ := fun k => 4 * ‖G.v (kidx k)‖ with hwdef
  have hv1 : ∀ i, 1 ≤ ‖G.v i‖ := hG.one_le_norm
  set A : ℝ := 1000 * (G.d + 1) / η with hA
  have hd0 : (0 : ℝ) ≤ G.d := Nat.cast_nonneg _
  have hApos : 0 < A := by positivity
  have hwM : ∀ i, A * ‖G.v i‖ ≤ wM G η i := fun i => Nat.le_ceil _
  have hwMpos : ∀ i, (0 : ℝ) < wM G η i := fun i =>
    lt_of_lt_of_le (mul_pos hApos (by linarith [hv1 i])) (hwM i)
  have hM1 : ∀ k, 1 ≤ M k := fun k => by
    have := hwMpos (kidx k)
    have : 0 < M k := by exact_mod_cast this
    omega
  set δ : ℝ := η / 16 with hδdef
  have hWM : ∑ k, w k / M k < δ / 4 := by
    have hk : ∀ k, w k / M k ≤ 4 / A := by
      intro k
      have h1 := hwM (kidx k)
      have h2 := hv1 (kidx k)
      rw [div_le_div_iff₀ (by exact_mod_cast (hM1 k) : (0 : ℝ) < M k) hApos]
      simp only [hwdef, hMdef]
      nlinarith
    calc ∑ k, w k / M k ≤ ∑ _k : K3 G.d, 4 / A := sum_le_sum fun k _ => hk k
      _ = 3 * G.d * (4 / A) := by
          rw [sum_const, card_univ, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
      _ < δ / 4 := by
          rw [hA, hδdef]
          field_simp
          nlinarith
  set P : ℝ := ∏ k, (2 * M k : ℝ) with hPdef
  set Ms : ℝ := ∑ k, (2 * M k : ℝ) with hMsdef
  set Ws : ℝ := ∑ k, w k with hWsdef
  have hδ0 : 0 < δ := by positivity
  have hP0 : 0 ≤ P := prod_nonneg fun k _ => by positivity
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, 0 < N ∧
      Ws / δ + 16 * Real.pi * P * Ms / δ + Ms ≤ N :=
    ⟨⌈Ws / δ + 16 * Real.pi * P * Ms / δ + Ms⌉₊ + 1, by omega,
      (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)⟩
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hWs0 : 0 ≤ Ws := sum_nonneg fun k _ => by positivity
  have hMs0 : 0 ≤ Ms := sum_nonneg fun k _ => by positivity
  have hpiPMs : 0 ≤ 16 * Real.pi * P * Ms / δ := by positivity
  have hN2k : ∀ k, 2 * M k ≤ N := by
    intro k
    have h1 : (2 * M k : ℝ) ≤ Ms :=
      single_le_sum (f := fun k => (2 * M k : ℝ)) (fun k _ => by positivity) (mem_univ k)
    have h2 : (2 * M k : ℝ) ≤ N := by linarith [div_nonneg hWs0 hδ0.le]
    exact_mod_cast h2
  have hN1 : ∑ k, w k / N ≤ δ := by
    rw [← sum_div, div_le_iff₀ hNr]
    have : Ws / δ ≤ N := by linarith [div_nonneg hWs0 hδ0.le]
    rw [div_le_iff₀ hδ0] at this
    linarith
  have hN2 : 2 * 2 * P * (Real.pi * ∑ k, (2 * M k : ℝ) / N) ≤ δ / 4 := by
    rw [← sum_div]
    have h16 : 16 * Real.pi * P * Ms / δ ≤ N := by linarith [div_nonneg hWs0 hδ0.le]
    rw [div_le_iff₀ hδ0] at h16
    rw [show 2 * 2 * P * (Real.pi * (Ms / N)) = (4 * Real.pi * P * Ms) / N by ring,
      div_le_iff₀ hNr]
    nlinarith [Real.pi_pos]
  -- grid means
  set T : ℝ := ((N : ℝ) ^ G.d) ^ 3 with hT
  have hT0 : 0 < T := by positivity
  have hcard : (Fintype.card (K3 G.d → ZMod N) : ℝ) = T := card_K3_fun G.d N
  set μ1 : ℝ := (∑ g : K3 G.d → ZMod N, F1 G F (gridPt g)) / T with hμ1
  set μ3 : ℝ := (∑ g : K3 G.d → ZMod N, F3 G F (gridPt g)) / T with hμ3
  have hμ : μ1 ^ 4 ≤ μ3 := grid_mean_ineq F N
  have hμ1b : |μ1| ≤ 1 := by
    rw [hμ1, abs_div, abs_of_pos hT0, div_le_one hT0, ← hcard]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ g : K3 G.d → ZMod N, |F1 G F (gridPt g)| ≤ ∑ _g : K3 G.d → ZMod N, (1 : ℝ) :=
          sum_le_sum fun g _ => hF1 _
      _ = _ := by simp
  have hF3b : ∀ X, |F3 G F X| ≤ 1 := by
    intro X
    unfold F3
    rw [abs_mul, abs_mul, abs_mul]
    have := hF1 (fun i => X (.inl i))
    have := hF1 (fun i => X (.inr (.inl i)))
    have := hF1 (fun i => X (.inr (.inr i)))
    have := hF1 (fun i => X (.inl i) - 3 • X (.inr (.inl i)) + 3 • X (.inr (.inr i)))
    calc _ ≤ (1 : ℝ) * 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  -- the points
  set ξ : ι → K3 G.d → UnitAddCircle := fun j => pack3 (x0 j) (x1 j) (x2 j) with hξ
  have hE1 : ∑ j, ω j * F1 G F (ξ j) = ∑ j, ω j * F (x0 j) := rfl
  have hE3 : ∑ j, ω j * F3 G F (ξ j) =
      ∑ j, ω j * (F (x0 j) * F (x1 j) * F (x2 j) * F (x3 j)) := by
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : ω j = 0
    · simp [hj]
    · rw [hx3 j hj]; rfl
  set E1 := ∑ j, ω j * F (x0 j) with hE1def
  set E3 := ∑ j, ω j * (F (x0 j) * F (x1 j) * F (x2 j) * F (x3 j)) with hE3def
  have hE1b : |E1| ≤ 1 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |ω j * F (x0 j)| ≤ ∑ j, ω j := sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_nonneg (hω0 j)]
          exact mul_le_of_le_one_right (hω0 j) (hF1 _)
      _ = 1 := hω1
  have hsub : ∀ (H : (K3 G.d → UnitAddCircle) → ℝ) (c : ℝ),
      ∑ j, ω j * (H (ξ j) - c) = ∑ j, ω j * H (ξ j) - c := by
    intro H c
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hω1, one_mul]
  have hmean0 : ∀ (H : (K3 G.d → UnitAddCircle) → ℝ),
      ∑ g : K3 G.d → ZMod N, (H (gridPt g) - (∑ g : K3 G.d → ZMod N, H (gridPt g)) / T) = 0 := by
    intro H
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hcard]
    field_simp
    ring
  have hclip_const : ∀ (H : (K3 G.d → UnitAddCircle) → ℝ) (c : ℝ), CLip w H →
      CLip w (fun X => H X - c) := by
    intro H c hH t t'
    simp only [sub_sub_sub_cancel_right]
    exact hH t t'
  obtain ⟨Ft, hFtL, hFtB, hFtm, hFtδ⟩ : ∃ Ft : (K3 G.d → UnitAddCircle) → ℝ, CLip w Ft ∧
      (∀ X, |Ft X| ≤ 2) ∧ ∑ g : K3 G.d → ZMod N, Ft (gridPt g) = 0 ∧
      δ ≤ |∑ j, ω j * Ft (ξ j)| := by
    by_cases hc : δ ≤ |E1 - μ1|
    · refine ⟨fun X => F1 G F X - μ1, hclip_const _ _ (clip_F1 hF), fun X => ?_, hmean0 _, ?_⟩
      · refine (abs_sub _ _).trans ?_
        have := hF1 (fun i => X (.inl i))
        unfold F1; linarith
      · rw [hsub, hE1]; exact hc
    · push_neg at hc
      refine ⟨fun X => F3 G F X - μ3, hclip_const _ _ (clip_F3 hF hF1), fun X => ?_, hmean0 _, ?_⟩
      · refine (abs_sub _ _).trans ?_
        have := hF3b X
        have : |μ3| ≤ 1 := by
          rw [hμ3, abs_div, abs_of_pos hT0, div_le_one hT0, ← hcard]
          refine (abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ g : K3 G.d → ZMod N, |F3 G F (gridPt g)| ≤ ∑ _g : K3 G.d → ZMod N, (1 : ℝ) :=
                sum_le_sum fun g _ => hF3b _
            _ = _ := by simp
        linarith
      · rw [hsub, hE3]
        have h4 := abs_pow_four_sub_le hE1b hμ1b
        have h5 : E1 ^ 4 - μ1 ^ 4 ≤ 4 * |E1 - μ1| := (le_abs_self _).trans h4
        rw [abs_sub_comm]
        refine le_trans ?_ (le_abs_self _)
        rw [hδdef] at hc ⊢
        linarith
  obtain ⟨k, hk0, hkM, hk⟩ := weyl_torus (N := N) hM1 hN2k (w := w) (B := 2) (δ := δ)
    (fun k => by positivity) hFtL hFtB hFtm hWM hN1 hN2 ω
    (by simp only [abs_of_nonneg (hω0 _)]; exact hω1.le) ξ hFtδ
  refine ⟨fun i => k (.inl i), fun i => k (.inr (.inl i)), fun i => k (.inr (.inr i)), ?_,
    fun i => ⟨hkM (.inl i), hkM (.inr (.inl i)), hkM (.inr (.inr i))⟩, ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨h0, h1, h2⟩ := hcon
    apply hk0
    funext κ
    rcases κ with i | i | i
    · exact congrFun h0 i
    · exact congrFun h1 i
    · exact congrFun h2 i
  · have htch : ∀ j, tch k (ξ j) = ec (kdot (fun i => k (.inl i)) (x0 j) +
        kdot (fun i => k (.inr (.inl i))) (x1 j) + kdot (fun i => k (.inr (.inr i))) (x2 j)) := by
      intro j
      unfold tch ec
      congr 3
      rw [sum_K3, kdot_apply, kdot_apply, kdot_apply, add_assoc]
      rfl
    simp only [htch] at hk
    have hPe : P = (∏ i, (2 * wM G η i : ℝ)) ^ 3 := by
      rw [hPdef, prod_K3]; simp only [hMdef, kidx, Sum.elim_inl, Sum.elim_inr, id]; ring
    rw [← hPe]
    have hP1 : 0 < P := prod_pos fun k _ => by have := hM1 k; positivity
    rw [div_le_iff₀ (by positivity)]
    rw [hδdef] at hk
    linarith

end

end GT
end File_GT_WeylStep

section File_GT_Prop71
/-!
# Proposition 7.1 of Green–Tao

A poorly distributed label gives a primitive dual frequency `k'`, a multiplier `m`, and for each
base point `a` of the Bohr set a frequency `ξ_a`, such that `k'·(Ξ(a + 2mh) − Ξ(a))` is small
for `h` in a small Bohr set with frequencies `S ∪ {ξ_a}`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma kdot_zero_left {ι : Type*} [Fintype ι] (y : ι → UnitAddCircle) :
    kdot (0 : ι → ℤ) y = 0 := by simp [kdot_apply]

lemma kdot_smul_left {ι : Type*} [Fintype ι] (c : ℤ) (k : ι → ℤ) (y : ι → UnitAddCircle) :
    kdot (c • k) y = c • kdot k y := by
  simp only [kdot_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, SemigroupAction.mul_smul]

/-- Rewriting a sum over pairs against a product weight as a double sum. -/
lemma sum_pair_weight (P Q : ZMod p → ℝ) (f : ZMod p × ZMod p → ℂ) :
    ∑ z : ZMod p × ZMod p, ((P z.1 * Q z.2 : ℝ) : ℂ) * f z =
      ∑ a, ∑ r, (P a : ℂ) * (Q r : ℂ) * f (a, r) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun r _ => ?_
  push_cast; ring

variable {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M] {n0 : ZMod p} {ρ : ℝ}
  {Ξ : ZMod p → M}

/-- Along a 4-term progression inside the Bohr set, a locally quadratic map satisfies
`Ξ(a + 3r) = Ξ(a) − 3Ξ(a + r) + 3Ξ(a + 2r)`. -/
lemma lq_ap3 (hL : LocQuad (sBohr S n0 ρ) Ξ) (hρ : 0 ≤ ρ) {a r : ZMod p}
    (hs : snorm S (a - n0) + 3 * snorm S r ≤ ρ) :
    Ξ (a + 3 * r) = Ξ a - 3 • Ξ (a + r) + 3 • Ξ (a + 2 * r) := by
  have hr := snorm_nonneg (S := S) r
  have h2 := lq_prog hL hρ (a := a) (h := r) 2 (by push_cast; linarith)
  have h3 := lq_prog hL hρ (a := a) (h := r) 3 (by push_cast; linarith)
  simp only [Nat.cast_ofNat] at h2 h3
  rw [show Nat.choose 2 2 = 1 by rfl, one_smul] at h2
  rw [show Nat.choose 3 2 = 3 by rfl] at h3
  have e2 : Ξ (a + 2 * r) = Ξ a + (2 • (Ξ (a + r) - Ξ a) + D2 Ξ a r r) := by rw [← h2]; abel
  have e3 : Ξ (a + 3 * r) = Ξ a + (3 • (Ξ (a + r) - Ξ a) + 3 • D2 Ξ a r r) := by rw [← h3]; abel
  rw [e3, e2]
  simp only [smul_add, smul_sub, ← SemigroupAction.mul_smul]
  abel

/-- Replacing `a` by `a + r` in an average against `P_{ρ/2}(a - n₀) ⊗ P_{ρ_r}(r)`. -/
lemma shift_a_by_r {S : Finset (ZMod p)} {n0 : ZMod p} {ρ ρr : ℝ} (hρ : 0 < ρ) (hρr : 0 ≤ ρr)
    (h4 : 4 * ρr ≤ ρ / 2) (g : ZMod p → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) :
    ‖∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) * g (a + r) -
      ∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) * (regP S ρr r : ℂ) * g a‖ ≤
      50 * S.card * ρr / (ρ / 2) := by
  have hD := regP_isDist S hρr
  have e : ∀ f : ZMod p → ZMod p → ℂ, ∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
      (regP S ρr r : ℂ) * f a r = ∑ r, (regP S ρr r : ℂ) *
        ∑ x, (regP S (ρ / 2) x : ℂ) * f (x + n0) r := by
    intro f
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum]
    rw [sum_regP_shift_center (S := S) (ρ := ρ / 2) n0
      (fun a w => (w : ℂ) * (regP S ρr r : ℂ) * f a r)]
    exact sum_congr rfl fun x _ => by ring
  rw [e (fun a r => g (a + r)), e (fun a _ => g a), ← sum_sub_distrib]
  simp only [← mul_sub]
  refine norm_wavg_le hD.1 hD.2 _ fun r hr => ?_
  have hrb : r ∈ bohr S ρr := mem_bohr_of_regP_ne_zero hρr hr
  have := regP_shift (Γ := S) (Γ' := S) subset_rfl (by positivity : (0 : ℝ) < ρ / 2) hρr h4 hrb
    (fun x => g (x + n0)) (fun x => hg _)
  simp only [one_mul] at this
  refine le_trans (le_of_eq ?_) this
  congr 2
  refine sum_congr rfl fun x _ => ?_
  rw [add_right_comm]

lemma one_le_wM {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (i : Fin G.d) :
    1 ≤ wM G η i := by
  have h1 := hG.one_le_norm i
  have h2 : (1 : ℝ) ≤ 1000 * (G.d + 1) / η * ‖G.v i‖ := by
    have : (1 : ℝ) ≤ 1000 * (G.d + 1) / η := by
      rw [le_div_iff₀ hη]; have : (0 : ℝ) ≤ G.d := Nat.cast_nonneg _; nlinarith
    nlinarith
  have := h2.trans (Nat.le_ceil _)
  unfold wM
  exact_mod_cast this

lemma one_le_wP {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 1 ≤ wP G η := by
  unfold wP
  refine one_le_pow₀ ?_
  calc (1 : ℝ) = ∏ _i : Fin G.d, (1 : ℝ) := by simp
    _ ≤ ∏ i, (2 * wM G η i : ℝ) := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => by
        have := one_le_wM hG hη hη1 i
        have : (1 : ℝ) ≤ wM G η i := by exact_mod_cast this
        linarith

lemma wδ_pos {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 0 < wδ G η := by
  unfold wδ; have := one_le_wP hG hη hη1; positivity

lemma wδ_le {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : wδ G η ≤ η / 256 := by
  unfold wδ
  have := one_le_wP hG hη hη1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Proposition 7.1, first half**: a poorly distributed label gives a non-zero `k_φ` with
`|k_{φ,i}| < 4 M_i` and a large correlation of the second difference of `k_φ · Ξ`. -/
theorem poor_d2 {S : Finset (ZMod p)} {n0 : ZMod p} {ρ : ℝ} (hρ : 0 < ρ)
    {ε4 : ℝ} (hε0 : 0 < ε4) (hε8 : ε4 ≤ 1 / 8)
    {G : DTorus} (hG : G.Good) {F : G.Pt → ℝ} (hF : G.IsLip F) (hF1 : ∀ x, |F x| ≤ 1)
    {Ξ : ZMod p → G.Pt} (hL : LocQuad (sBohr S n0 ρ) Ξ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsmall : 100 * S.card * ε4 ≤ wδ G η / 2)
    (hpoor : ∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        (F (Ξ z.1) * F (Ξ (z.1 + z.2)) * F (Ξ (z.1 + 2 * z.2)) * F (Ξ (z.1 + 3 * z.2))) <
      (∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        F (Ξ z.1)) ^ 4 - η / 2) :
    ∃ kφ : Fin G.d → ℤ, kφ ≠ 0 ∧ (∀ i, |kφ i| < 4 * wM G η i) ∧
      ∃ a0, snorm S (a0 - n0) ≤ ρ / 2 ∧
      ∃ b1 b2 : ZMod p → ℂ, (∀ r, ‖b1 r‖ ≤ 1) ∧ (∀ h, ‖b2 h‖ ≤ 1) ∧
        wδ G η / 4 ≤ ‖∑ r, ∑ h, (regP S (ε4 * ρ) r : ℂ) * (regP S (wρh S G η ε4 ρ) h : ℂ) *
          (b1 r * b2 h * ec (D2 (fun x => kdot kφ (Ξ x)) a0 r h))‖ := by
  classical
  set P1 : ZMod p → ℝ := fun a => regP S (ρ / 2) (a - n0) with hP1
  set P2 : ZMod p → ℝ := regP S (ε4 * ρ) with hP2
  set ω : ZMod p × ZMod p → ℝ := fun z => P1 z.1 * P2 z.2 with hω
  have hρr : 0 < ε4 * ρ := mul_pos hε0 hρ
  have hω0 : ∀ z, 0 ≤ ω z := fun z => mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)
  have hω1 : ∑ z, ω z = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hω, ← mul_sum, ← sum_mul]
    rw [sum_regP S hρr.le, mul_one]
    exact sum_regP_center S (by positivity) n0
  have hsupp : ∀ z, ω z ≠ 0 → snorm S (z.1 - n0) ≤ ρ / 2 ∧ snorm S z.2 ≤ ε4 * ρ := by
    intro z hz
    have h1 : P1 z.1 ≠ 0 := fun h => hz (by simp [hω, h])
    have h2 : P2 z.2 ≠ 0 := fun h => hz (by simp [hω, h])
    exact ⟨snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) h1) (by positivity),
      snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρr.le h2) hρr.le⟩
  have hx3 : ∀ z, ω z ≠ 0 → Ξ (z.1 + 3 * z.2) = Ξ z.1 - 3 • Ξ (z.1 + z.2) +
      3 • Ξ (z.1 + 2 * z.2) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hsupp z hz
    exact lq_ap3 hL hρ.le (by nlinarith)
  obtain ⟨k0, k1, k2, hnz, hkb, hbig⟩ := weyl_step hG hF hF1 ω hω0 hω1
    (fun z => Ξ z.1) (fun z => Ξ (z.1 + z.2)) (fun z => Ξ (z.1 + 2 * z.2))
    (fun z => Ξ (z.1 + 3 * z.2)) hx3 hη hpoor
  change wδ G η ≤ _ at hbig
  have hδ0 := wδ_pos hG hη hη1
  have hδle := wδ_le hG hη hη1
  set δ := wδ G η with hδ
  set ρh := wρh S G η ε4 ρ with hρhdef
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hρh0 : 0 < ρh := by rw [hρhdef, wρh]; positivity
  have hρh1 : ρh ≤ δ * ε4 * ρ / 1000 := by
    rw [hρhdef, wρh, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ δ * ε4 * ρ := by positivity
    nlinarith
  have h4 : 4 * ρh ≤ ρ / 2 := by
    have : δ * ε4 * ρ ≤ ρ := by
      have : δ * ε4 ≤ 1 := by nlinarith
      nlinarith
    linarith
  have h4r : 4 * ρh ≤ ε4 * ρ := by
    have : δ * ε4 * ρ ≤ ε4 * ρ := by
      have : δ ≤ 1 := by linarith
      nlinarith [mul_pos hε0 hρ]
    linarith
  have hsepgen : ∀ δ' : ℝ, δ / 2 ≤ δ' →
      50 * S.card * ρh / (ρ / 2) + 50 * S.card * ρh / (ε4 * ρ) ≤ δ' / 2 := by
    intro δ' hδ'
    have e : 50 * S.card * ρh / (ρ / 2) + 50 * S.card * ρh / (ε4 * ρ) =
        50 * S.card * δ * (2 * ε4 + 1) / (1000 * (S.card + 1)) := by
      rw [hρhdef, wρh]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  -- the double sum form of the Weyl conclusion
  set ψ : Fin G.d → ℤ → ZMod p → UnitAddCircle := fun k _ x => kdot k (Ξ x) with hψ
  have hbig2 : δ ≤ ‖∑ a, ∑ r, (P1 a : ℂ) * (P2 r : ℂ) *
      ec (kdot k0 (Ξ a) + kdot k1 (Ξ (a + r)) + kdot k2 (Ξ (a + 2 * r)))‖ := by
    rw [← sum_pair_weight P1 P2 (fun z => ec (kdot k0 (Ξ z.1) + kdot k1 (Ξ (z.1 + z.2)) +
      kdot k2 (Ξ (z.1 + 2 * z.2))))]
    exact hbig
  have hLk : ∀ k : Fin G.d → ℤ, LocQuad (sBohr S n0 ρ) (fun x => kdot k (Ξ x)) :=
    fun k => hL.comp (kdot k)
  by_cases hk2 : k2 = 0
  · by_cases hk1 : k1 = 0
    · -- only `k₀` survives
      have hk0 : k0 ≠ 0 := by
        rcases hnz with h | h | h
        · exact h
        · exact absurd hk1 h
        · exact absurd hk2 h
      subst hk2; subst hk1
      simp only [kdot_zero_left, add_zero] at hbig2
      have hsh := shift_a_by_r (S := S) (n0 := n0) hρ hρr.le (by nlinarith)
        (fun x => ec (kdot k0 (Ξ x))) (fun x => by simp)
      have hbig3 : δ / 2 ≤ ‖∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) * (regP S (ε4 * ρ) r : ℂ) *
          ec ((0 : ZMod p → UnitAddCircle) a + kdot k0 (Ξ (a + r)))‖ := by
        simp only [Pi.zero_apply, zero_add]
        have e1 : 50 * S.card * (ε4 * ρ) / (ρ / 2) = 100 * S.card * ε4 := by
          field_simp; ring
        rw [e1] at hsh
        have := norm_sub_norm_le (∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
          (regP S (ε4 * ρ) r : ℂ) * ec (kdot k0 (Ξ a)))
          (∑ a, ∑ r, (regP S (ρ / 2) (a - n0) : ℂ) *
          (regP S (ε4 * ρ) r : ℂ) * ec (kdot k0 (Ξ (a + r))))
        rw [norm_sub_rev] at this
        linarith
      obtain ⟨a0, ha0, b1, b2, hb1, hb2, hres⟩ := wd_head1 (S := S) (n0 := n0) hρ hρr hρh0 h4 h4r
        (hsepgen (δ / 2) le_rfl) 0 (fun x => kdot k0 (Ξ x)) hbig3
      refine ⟨k0, hk0, fun i => ?_, a0, ha0, b1, b2, hb1, hb2, ?_⟩
      · have := (hkb i).1; have := one_le_wM hG hη hη1 i; omega
      · linarith
    · -- `k₂ = 0`, `k₁ ≠ 0`
      subst hk2
      simp only [kdot_zero_left, add_zero] at hbig2
      obtain ⟨a0, ha0, b1, b2, hb1, hb2, hres⟩ := wd_head1 (S := S) (n0 := n0) hρ hρr hρh0 h4 h4r
        (hsepgen δ (by linarith)) (fun x => kdot k0 (Ξ x)) (fun x => kdot k1 (Ξ x)) hbig2
      refine ⟨k1, hk1, fun i => ?_, a0, ha0, b1, b2, hb1, hb2, ?_⟩
      · have := (hkb i).2.1; have := one_le_wM hG hη hη1 i; omega
      · linarith
  · -- `k₂ ≠ 0`
    have hbud : 2 * (ε4 * ρ) + ρh ≤ ρ / 2 := by nlinarith
    obtain ⟨a0, ha0, b1, b2, hb1, hb2, hres⟩ := wd_head2 (S := S) (n0 := n0) hρ hρr hρh0 h4 h4r
      hbud (hsepgen δ (by linarith)) (fun x => kdot k0 (Ξ x)) (fun x => kdot k1 (Ξ x))
      (fun x => kdot k2 (Ξ x)) (hLk k2) hbig2
    refine ⟨(2 : ℤ) • k2, fun h => hk2 ?_, fun i => ?_, a0, ha0, b1, b2, hb1, hb2, ?_⟩
    · funext i; have := congrFun h i; simp at this; exact this
    · have := (hkb i).2.2
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      norm_num; omega
    · have e : (fun x => 2 • kdot k2 (Ξ x)) = fun x => kdot ((2 : ℤ) • k2) (Ξ x) := by
        funext x; rw [kdot_smul_left]; norm_cast
      rw [e] at hres
      linarith

end

end GT
end File_GT_Prop71

open Finset KM
open scoped ComplexConjugate
open GT in
theorem solution {p : ℕ} [NeZero p] {S : Finset (ZMod p)} {n0 : ZMod p} {ρ : ℝ} (hρ : 0 < ρ)
    {ε4 : ℝ} (hε0 : 0 < ε4) (hε8 : ε4 ≤ 1 / 8)
    {G : DTorus} (hG : G.Good) {F : G.Pt → ℝ} (hF : G.IsLip F) (hF1 : ∀ x, |F x| ≤ 1)
    {Ξ : ZMod p → G.Pt} (hL : LocQuad (sBohr S n0 ρ) Ξ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsmall : 100 * S.card * ε4 ≤ wδ G η / 2)
    (hpoor : ∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        (F (Ξ z.1) * F (Ξ (z.1 + z.2)) * F (Ξ (z.1 + 2 * z.2)) * F (Ξ (z.1 + 3 * z.2))) <
      (∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        F (Ξ z.1)) ^ 4 - η / 2) :
    ∃ kφ : Fin G.d → ℤ, kφ ≠ 0 ∧ (∀ i, |kφ i| < 4 * wM G η i) ∧
      ∃ a0, snorm S (a0 - n0) ≤ ρ / 2 ∧
      ∃ b1 b2 : ZMod p → ℂ, (∀ r, ‖b1 r‖ ≤ 1) ∧ (∀ h, ‖b2 h‖ ≤ 1) ∧
        wδ G η / 4 ≤ ‖∑ r, ∑ h, (regP S (ε4 * ρ) r : ℂ) * (regP S (wρh S G η ε4 ρ) h : ℂ) *
          (b1 r * b2 h * ec (D2 (fun x => kdot kφ (Ξ x)) a0 r h))‖ :=
  @GT.poor_d2 p _ S n0 ρ hρ ε4 hε0 hε8 G hG F hF hF1 Ξ hL η hη hη1 hsmall hpoor

