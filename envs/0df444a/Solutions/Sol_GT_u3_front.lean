-- Prove2me | solution 1 for GT.u3_front
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:48.333259+00:00
-- url     : https://prove2.me/submissions/aae3a49d-02ea-4550-b21c-7a43bde0c0f9

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_u3_step3

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

/-- The (unnormalised) Fourier transform of a complex function. -/
def cft (g : ZMod N → ℂ) (ξ : ZMod N) : ℂ := ∑ x, g x * ech (-(ξ * x))

lemma conj_cft (g : ZMod N → ℂ) (ξ : ZMod N) :
    conj (cft g ξ) = ∑ x, conj (g x) * ech (ξ * x) := by
  simp only [cft, map_sum, map_mul, ← ech_neg, neg_neg]

/-- Shifted Parseval identity. -/
lemma sum_shift_mul_conj (g : ZMod N → ℂ) (a b : ZMod N) :
    ∑ h, g (h + a) * conj (g (h + b)) =
      (1 / N : ℂ) * ∑ ξ, ((‖cft g ξ‖ ^ 2 : ℝ) : ℂ) * ech (ξ * (a - b)) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have e1 : ∀ ξ, ((‖cft g ξ‖ ^ 2 : ℝ) : ℂ) * ech (ξ * (a - b)) =
      ∑ x, ∑ y, g x * conj (g y) * ech (ξ * (y - x + (a - b))) := by
    intro ξ
    rw [show ((‖cft g ξ‖ ^ 2 : ℝ) : ℂ) = cft g ξ * conj (cft g ξ) by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    rw [conj_cft, cft, sum_mul, sum_mul]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun y _ => ?_
    rw [show ξ * (y - x + (a - b)) = -(ξ * x) + ξ * y + ξ * (a - b) by ring, ech_add, ech_add]
    ring
  simp_rw [e1]
  rw [sum_comm, mul_sum]
  have e3 : ∀ x y, (1 / N : ℂ) * ∑ ξ, g x * conj (g y) * ech (ξ * (y - x + (a - b))) =
      if y = x - a + b then g x * conj (g y) else 0 := by
    intro x y
    rw [← mul_sum, sum_ech_mul]
    by_cases hxy : y = x - a + b
    · rw [if_pos (by rw [hxy]; ring), if_pos hxy]; field_simp
    · rw [if_neg (by intro h; apply hxy; linear_combination h), if_neg hxy]; simp
  rw [eq_comm, sum_congr rfl fun x _ => by rw [sum_comm, mul_sum]]
  simp_rw [e3, sum_ite_eq', mem_univ, if_true]
  exact Fintype.sum_equiv (Equiv.subRight a) _ _ fun h => by simp

lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma sum_comm3 {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, f a b c := by
  rw [sum_comm]; exact sum_congr rfl fun b _ => sum_comm

/-- Parseval. -/
lemma parseval_c (g : ZMod N → ℂ) : ∑ x, ‖g x‖ ^ 2 = (1 / N : ℝ) * ∑ ξ, ‖cft g ξ‖ ^ 2 := by
  have h := sum_shift_mul_conj g 0 0
  simp only [add_zero, sub_self, mul_zero, ech_zero, mul_one, ← ofReal_norm_sq] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  exact h

/-- The Fourier weight appearing in the `U²` inverse theorem. -/
def u2A (w : ZMod N → ℝ) (g : ZMod N → ℂ) (ξ : ZMod N) : ℝ :=
  ∑ h, ‖∑ a, (w a : ℂ) * g (h + a) * ech (-(ξ * a))‖ ^ 2

lemma u2A_nonneg (w : ZMod N → ℝ) (g : ZMod N → ℂ) (ξ : ZMod N) : 0 ≤ u2A w g ξ :=
  sum_nonneg fun _ _ => sq_nonneg _

lemma u2_identity (w : ZMod N → ℝ) (g : ZMod N → ℂ) :
    ∑ a, ∑ b, w a * w b * ‖∑ h, g (h + a) * conj (g (h + b))‖ ^ 2 =
      (1 / N : ℝ) * ∑ ξ, ‖cft g ξ‖ ^ 2 * u2A w g ξ := by
  set G : ZMod N → ZMod N → ℂ := fun a b => ∑ h, g (h + a) * conj (g (h + b)) with hGdef
  set c : ZMod N → ℂ := fun ξ => ((‖cft g ξ‖ ^ 2 : ℝ) : ℂ) with hcdef
  have hc : ∀ a b, conj (G a b) = (1 / N : ℂ) * ∑ ξ, c ξ * (ech (-(ξ * a)) * ech (ξ * b)) := by
    intro a b
    rw [hGdef]; (try dsimp only)
    rw [sum_shift_mul_conj, map_mul, map_sum]
    congr 1
    · simp
    · refine sum_congr rfl fun ξ _ => ?_
      rw [map_mul, Complex.conj_ofReal, ← ech_neg, ← ech_add]
      congr 2; ring
  have hA : ∀ ξ, ((u2A w g ξ : ℝ) : ℂ) =
      ∑ a, ∑ b, (w a : ℂ) * w b * G a b * (ech (-(ξ * a)) * ech (ξ * b)) := by
    intro ξ
    simp only [u2A, Complex.ofReal_sum, ofReal_norm_sq]
    simp_rw [map_sum, map_mul, Complex.conj_ofReal, ← ech_neg, neg_neg, sum_mul, mul_sum]
    refine (sum_comm3 _ _ _ _).trans (sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_)
    rw [hGdef]; (try dsimp only)
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun h _ => ?_
    ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  simp_rw [hA]
  have hL : ∀ a b, ((‖∑ h, g (h + a) * conj (g (h + b))‖ ^ 2 : ℝ) : ℂ) =
      G a b * ((1 / N : ℂ) * ∑ ξ, c ξ * (ech (-(ξ * a)) * ech (ξ * b))) := by
    intro a b; rw [ofReal_norm_sq]; exact congrArg (fun z => G a b * z) (hc a b)
  simp_rw [hL]
  simp only [mul_sum]
  conv_rhs => rw [sum_comm3]
  push_cast
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun ξ _ => ?_
  rw [hcdef]; push_cast
  ring

/-! ### Elementary estimates -/

lemma sum_shift' {M : Type*} [AddCommMonoid M] (F : ZMod N → M) (t : ZMod N) :
    ∑ x, F (x + t) = ∑ x, F x :=
  Fintype.sum_equiv (Equiv.addRight t) _ _ fun _ => rfl

/-- Total variation between `P` and its translate by `b`. -/
def tvs (P : ZMod N → ℝ) (b : ZMod N) : ℝ := ∑ x, |P (x + b) - P x|

lemma sq_sqrt_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (√x - √y) ^ 2 ≤ |x - y| := by
  have hx' := Real.sq_sqrt hx
  have hy' := Real.sq_sqrt hy
  have h0x := Real.sqrt_nonneg x
  have h0y := Real.sqrt_nonneg y
  have e : x - y = (√x - √y) * (√x + √y) := by nlinarith
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ √x + √y), sq]
  rw [← sq, ← sq_abs]
  rw [sq]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [abs_le]; constructor <;> nlinarith

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

lemma sum_sqrt_mul_abs_sub_le (a b : ZMod N) :
    ∑ x, √(P (x + a)) * |√(P (x + b)) - √(P x)| ≤ √(tvs P b) := by
  have h0 : 0 ≤ ∑ x, √(P (x + a)) * |√(P (x + b)) - √(P x)| :=
    sum_nonneg fun _ _ => by positivity
  rw [← Real.sqrt_sq h0]
  apply Real.sqrt_le_sqrt
  refine (sum_mul_sq_le_sq_mul_sq univ (fun x => √(P (x + a)))
    (fun x => |√(P (x + b)) - √(P x)|)).trans ?_
  have e1 : ∑ x, √(P (x + a)) ^ 2 = 1 := by
    simp_rw [Real.sq_sqrt (hP _)]; rw [sum_shift' P a]; exact hP1
  rw [e1, one_mul]
  exact sum_le_sum fun x _ => by rw [sq_abs]; exact sq_sqrt_sub_le (hP _) (hP _)

lemma sum_abs_sub_sqrt_mul_le (a b : ZMod N) :
    ∑ x, |P x - √(P (x + a)) * √(P (x + b))| ≤ √(tvs P a) + √(tvs P b) := by
  have key : ∀ x, |P x - √(P (x + a)) * √(P (x + b))| ≤
      √(P (x + a)) * |√(P (x + b)) - √(P x)| + √(P (x + 0)) * |√(P (x + a)) - √(P x)| := by
    intro x
    rw [add_zero]
    have e : P x - √(P (x + a)) * √(P (x + b)) =
        √(P (x + a)) * (√(P x) - √(P (x + b))) + √(P x) * (√(P x) - √(P (x + a))) := by
      have := Real.mul_self_sqrt (hP x); nlinarith
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      abs_sub_comm (√(P x)), abs_sub_comm (√(P x))]
  refine (sum_le_sum fun x _ => key x).trans ?_
  rw [sum_add_distrib]
  have h1 := sum_sqrt_mul_abs_sub_le hP hP1 a b
  have h2 := sum_sqrt_mul_abs_sub_le hP hP1 0 a
  linarith

lemma sum_sqrt_mul_sqrt_le (a b : ZMod N) : ∑ x, √(P (x + a)) * √(P (x + b)) ≤ 1 := by
  have key : ∀ x, √(P (x + a)) * √(P (x + b)) ≤ (P (x + a) + P (x + b)) / 2 := by
    intro x
    have h1 := Real.sq_sqrt (hP (x + a))
    have h2 := Real.sq_sqrt (hP (x + b))
    nlinarith [sq_nonneg (√(P (x + a)) - √(P (x + b)))]
  refine (sum_le_sum fun x _ => key x).trans (le_of_eq ?_)
  rw [← sum_div, sum_add_distrib, sum_shift' P a, sum_shift' P b, hP1]; norm_num

end dist

/-! ### The main estimates -/

section main

variable {P0 P1 : ZMod N → ℝ} (hP0 : ∀ x, 0 ≤ P0 x) (hP0s : ∑ x, P0 x = 1)
  (hP1 : ∀ x, 0 ≤ P1 x) (hP1s : ∑ x, P1 x = 1) {ε : ℝ} (hε : 0 ≤ ε)
  (hTV : ∀ b, P1 b ≠ 0 → tvs P0 b ≤ ε)

include hP0 hP0s hP1 hP1s hTV in
/-- Replacing `√P₀(n₀ + n₁)` by `√P₀(n₀)` in the Fourier weight. -/
lemma u2A_le_corr (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (ξ : ZMod N) :
    u2A P1 (fun x => f x * (√(P0 x) : ℂ)) ξ ≤
      ∑ n0, P0 n0 * ‖∑ n1, (P1 n1 : ℂ) * f (n0 + n1) * ech (-(ξ * n1))‖ ^ 2 + 2 * √ε := by
  set s : ZMod N → ℝ := fun x => √(P0 x) with hs
  have hs0 : ∀ x, 0 ≤ s x := fun x => Real.sqrt_nonneg _
  have hs2 : ∀ x, s x ^ 2 = P0 x := fun x => Real.sq_sqrt (hP0 x)
  set U : ZMod N → ℂ := fun h => ∑ a, (P1 a : ℂ) * (f (h + a) * (s (h + a) : ℂ)) * ech (-(ξ * a))
    with hU
  set W : ZMod N → ℂ := fun h => ∑ a, (P1 a : ℂ) * f (h + a) * ech (-(ξ * a)) with hW
  set V : ZMod N → ℂ := fun h => (s h : ℂ) * W h with hV
  have hA : u2A P1 (fun x => f x * (√(P0 x) : ℂ)) ξ = ∑ h, ‖U h‖ ^ 2 := rfl
  have hB : ∑ n0, P0 n0 * ‖W n0‖ ^ 2 = ∑ h, ‖V h‖ ^ 2 := by
    refine sum_congr rfl fun h _ => ?_
    rw [hV]; (try dsimp only)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs0 h), mul_pow, hs2]
  rw [hA, show (∑ n0, P0 n0 * ‖∑ n1, (P1 n1 : ℂ) * f (n0 + n1) * ech (-(ξ * n1))‖ ^ 2) =
    ∑ n0, P0 n0 * ‖W n0‖ ^ 2 from rfl, hB]
  -- pointwise bounds
  have hUb : ∀ h, ‖U h‖ ≤ ∑ a, P1 a * s (h + a) := by
    intro h
    refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_ech, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hP1 a), abs_of_nonneg (hs0 _), mul_one]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (hs0 _) (hf _)) (hP1 a)
  have hWb : ∀ h, ‖W h‖ ≤ 1 := by
    intro h
    refine (norm_sum_le _ _).trans ((sum_le_sum fun a _ => ?_).trans (le_of_eq hP1s))
    rw [norm_mul, norm_mul, norm_ech, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP1 a),
      mul_one]
    exact mul_le_of_le_one_right (hP1 a) (hf _)
  have hVb : ∀ h, ‖V h‖ ≤ s h := by
    intro h
    rw [hV]; (try dsimp only)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs0 h)]
    exact mul_le_of_le_one_right (hs0 h) (hWb h)
  have hUVb : ∀ h, ‖U h - V h‖ ≤ ∑ a, P1 a * |s (h + a) - s h| := by
    intro h
    have e : U h - V h = ∑ a, (P1 a : ℂ) * f (h + a) * ((s (h + a) - s h : ℝ) : ℂ) *
        ech (-(ξ * a)) := by
      rw [hU, hV, hW]; (try dsimp only)
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun a _ => ?_
      push_cast; ring
    rw [e]
    refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_ech, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hP1 a), mul_one]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hP1 a) (hf _)) (abs_nonneg _)
  -- summed bounds
  have hUsq : ∑ h, ‖U h‖ ^ 2 ≤ 1 := by
    calc ∑ h, ‖U h‖ ^ 2 ≤ ∑ h, ∑ a, P1 a * s (h + a) ^ 2 := sum_le_sum fun h _ =>
          (pow_le_pow_left₀ (norm_nonneg _) (hUb h) 2).trans (sq_wavg_le _ hP1 hP1s)
      _ = 1 := by
          rw [sum_comm]
          simp_rw [hs2, ← mul_sum, sum_shift' P0, hP0s, mul_one, hP1s]
  have hVsq : ∑ h, ‖V h‖ ^ 2 ≤ 1 := by
    calc ∑ h, ‖V h‖ ^ 2 ≤ ∑ h, s h ^ 2 := sum_le_sum fun h _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hVb h) 2
      _ = 1 := by simp_rw [hs2, hP0s]
  have hUVsq : ∑ h, ‖U h - V h‖ ^ 2 ≤ ε := by
    calc ∑ h, ‖U h - V h‖ ^ 2 ≤ ∑ h, ∑ a, P1 a * |P0 (h + a) - P0 h| := sum_le_sum fun h _ =>
          ((pow_le_pow_left₀ (norm_nonneg _) (hUVb h) 2).trans (sq_wavg_le _ hP1 hP1s)).trans
            (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
              (by rw [sq_abs]; exact sq_sqrt_sub_le (hP0 _) (hP0 _)) (hP1 a))
      _ = ∑ a, P1 a * tvs P0 a := by rw [sum_comm]; simp_rw [← mul_sum]; rfl
      _ ≤ ∑ a, P1 a * ε := sum_le_sum fun a _ => by
          by_cases ha : P1 a = 0
          · rw [ha, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (hTV a ha) (hP1 a)
      _ = ε := by rw [← sum_mul, hP1s, one_mul]
  -- conclude
  have hpt : ∀ h, ‖U h‖ ^ 2 - ‖V h‖ ^ 2 ≤ ‖U h - V h‖ * (‖U h‖ + ‖V h‖) := by
    intro h
    have h1 : ‖U h‖ - ‖V h‖ ≤ ‖U h - V h‖ := norm_sub_norm_le _ _
    have h2 : 0 ≤ ‖U h‖ + ‖V h‖ := by positivity
    nlinarith
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ (fun h => ‖U h - V h‖)
    (fun h => ‖U h‖ + ‖V h‖)
  have hsum2 : ∑ h, (‖U h‖ + ‖V h‖) ^ 2 ≤ 4 := by
    calc ∑ h, (‖U h‖ + ‖V h‖) ^ 2 ≤ ∑ h, (2 * ‖U h‖ ^ 2 + 2 * ‖V h‖ ^ 2) :=
          sum_le_sum fun h _ => by nlinarith [sq_nonneg (‖U h‖ - ‖V h‖)]
      _ ≤ 4 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]; linarith
  have hs1 : √(∑ h, ‖U h - V h‖ ^ 2) ≤ √ε := Real.sqrt_le_sqrt hUVsq
  have hs4 : √(∑ h, (‖U h‖ + ‖V h‖) ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hsum2
  have hdiff : ∑ h, ‖U h‖ ^ 2 - ∑ h, ‖V h‖ ^ 2 ≤ 2 * √ε := by
    rw [← sum_sub_distrib]
    refine (sum_le_sum fun h _ => hpt h).trans (hcs.trans ?_)
    have := Real.sqrt_nonneg ε
    have := Real.sqrt_nonneg (∑ h, (‖U h‖ + ‖V h‖) ^ 2)
    nlinarith [Real.sqrt_nonneg (∑ h, ‖U h - V h‖ ^ 2)]
  linarith

lemma sum4_perm1 {M : Type*} [AddCommMonoid M] (F : ZMod N → ZMod N → ZMod N → ZMod N → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ b, ∑ c, ∑ d, ∑ a, F a b c d := by
  rw [sum_comm]; exact sum_congr rfl fun b _ => sum_comm3 _ _ _ _

lemma sum4_perm2 {M : Type*} [AddCommMonoid M] (F : ZMod N → ZMod N → ZMod N → ZMod N → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  rw [sum4_perm1, sum4_perm1]

lemma norm_sum4_sub_le (u v : ZMod N → ZMod N → ZMod N → ZMod N → ℝ)
    (X : ZMod N → ZMod N → ZMod N → ZMod N → ℂ) (hX : ∀ a b c d, ‖X a b c d‖ ≤ 1) :
    ‖(∑ a, ∑ b, ∑ c, ∑ d, (u a b c d : ℂ) * X a b c d) -
      ∑ a, ∑ b, ∑ c, ∑ d, (v a b c d : ℂ) * X a b c d‖ ≤
      ∑ a, ∑ b, ∑ c, ∑ d, |u a b c d - v a b c d| := by
  simp only [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => (norm_sum_le _ _).trans
    (sum_le_sum fun b _ => (norm_sum_le _ _).trans (sum_le_sum fun c _ =>
      (norm_sum_le _ _).trans (sum_le_sum fun d _ => ?_))))
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (hX a b c d)

include hP0 hP0s hP1 hTV in
lemma sum_abs_sub_le_two_sqrt (h1 h1' : ZMod N) :
    P1 h1 * P1 h1' * ∑ h0, |P0 h0 - √(P0 (h0 + h1)) * √(P0 (h0 + h1'))| ≤
      P1 h1 * P1 h1' * (2 * √ε) := by
  by_cases h10 : P1 h1 = 0
  · simp [h10]
  by_cases h10' : P1 h1' = 0
  · simp [h10']
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hP1 _) (hP1 _))
  refine (sum_abs_sub_sqrt_mul_le hP0 hP0s h1 h1').trans ?_
  have := Real.sqrt_le_sqrt (hTV h1 h10)
  have := Real.sqrt_le_sqrt (hTV h1' h10')
  linarith

include hP0s hP1s in
lemma sum3_weights (c : ℝ) :
    ∑ a, ∑ b, ∑ d, P0 a * (P1 b * P1 d * c) = c := by
  have h1 : ∀ a b, ∑ d, P0 a * (P1 b * P1 d * c) = P0 a * P1 b * c := fun a b => by
    rw [sum_congr rfl fun d _ => (by ring : P0 a * (P1 b * P1 d * c) = P0 a * P1 b * c * P1 d),
      ← mul_sum, hP1s, mul_one]
  have h2 : ∀ a, ∑ b, P0 a * P1 b * c = P0 a * c := fun a => by
    rw [sum_congr rfl fun b _ => (by ring : P0 a * P1 b * c = P0 a * c * P1 b),
      ← mul_sum, hP1s, mul_one]
  simp_rw [h1, h2, ← sum_mul, hP0s, one_mul]

include hP0 hP0s hP1 hP1s hTV in
/-- Replacing `P₀(h₀)P₀(h₀')` by products of square roots (Shao's trick). -/
lemma u2_replace (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(∑ h0, ∑ h0', ∑ h1, ∑ h1', ((P0 h0 * P0 h0' * P1 h1 * P1 h1' : ℝ) : ℂ) *
      (f (h0 + h1) * conj (f (h0 + h1')) * conj (f (h0' + h1)) * f (h0' + h1'))) -
      ((∑ h1, ∑ h1', P1 h1 * P1 h1' *
        ‖∑ h, (f (h + h1) * (√(P0 (h + h1)) : ℂ)) *
          conj (f (h + h1') * (√(P0 (h + h1')) : ℂ))‖ ^ 2 : ℝ) : ℂ)‖ ≤ 4 * √ε := by
  set s : ZMod N → ℝ := fun x => √(P0 x) with hs
  have hs0 : ∀ x, 0 ≤ s x := fun x => Real.sqrt_nonneg _
  set X : ZMod N → ZMod N → ZMod N → ZMod N → ℂ := fun h0 h0' h1 h1' =>
    f (h0 + h1) * conj (f (h0 + h1')) * conj (f (h0' + h1)) * f (h0' + h1') with hX
  have hX1 : ∀ a b c d, ‖X a b c d‖ ≤ 1 := by
    intro a b c d
    simp only [hX, norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (hf _) (norm_nonneg _) (hf _)) (by positivity)
      (hf _)) (norm_nonneg _) (hf _)
  set w1 : ZMod N → ZMod N → ZMod N → ZMod N → ℝ := fun h0 h0' h1 h1' =>
    s (h0 + h1) * s (h0 + h1') * P0 h0' * P1 h1 * P1 h1' with hw1
  set w2 : ZMod N → ZMod N → ZMod N → ZMod N → ℝ := fun h0 h0' h1 h1' =>
    s (h0 + h1) * s (h0 + h1') * (s (h0' + h1) * s (h0' + h1')) * P1 h1 * P1 h1' with hw2
  have step1 : ‖(∑ h0, ∑ h0', ∑ h1, ∑ h1', ((P0 h0 * P0 h0' * P1 h1 * P1 h1' : ℝ) : ℂ) *
      X h0 h0' h1 h1') - ∑ h0, ∑ h0', ∑ h1, ∑ h1', (w1 h0 h0' h1 h1' : ℂ) * X h0 h0' h1 h1'‖ ≤
      2 * √ε := by
    refine (norm_sum4_sub_le _ _ X hX1).trans ?_
    have e : ∀ h0 h0' h1 h1', |P0 h0 * P0 h0' * P1 h1 * P1 h1' - w1 h0 h0' h1 h1'| =
        P0 h0' * (P1 h1 * P1 h1' * |P0 h0 - s (h0 + h1) * s (h0 + h1')|) := by
      intro h0 h0' h1 h1'
      rw [show P0 h0 * P0 h0' * P1 h1 * P1 h1' - w1 h0 h0' h1 h1' =
        (P0 h0' * (P1 h1 * P1 h1')) * (P0 h0 - s (h0 + h1) * s (h0 + h1')) by rw [hw1]; ring,
        abs_mul, abs_of_nonneg (mul_nonneg (hP0 _) (mul_nonneg (hP1 _) (hP1 _)))]
      ring
    simp_rw [e]
    rw [sum4_perm1]
    calc ∑ h0', ∑ h1, ∑ h1', ∑ h0, P0 h0' * (P1 h1 * P1 h1' * |P0 h0 - s (h0 + h1) * s (h0 + h1')|)
        ≤ ∑ h0', ∑ h1, ∑ h1', P0 h0' * (P1 h1 * P1 h1' * (2 * √ε)) := by
          refine sum_le_sum fun h0' _ => sum_le_sum fun h1 _ => sum_le_sum fun h1' _ => ?_
          rw [← mul_sum, ← mul_sum]
          exact mul_le_mul_of_nonneg_left
            (sum_abs_sub_le_two_sqrt hP0 hP0s hP1 hTV h1 h1') (hP0 h0')
      _ = 2 * √ε := sum3_weights hP0s hP1s _
  have step2 : ‖(∑ h0, ∑ h0', ∑ h1, ∑ h1', (w1 h0 h0' h1 h1' : ℂ) * X h0 h0' h1 h1') -
      ∑ h0, ∑ h0', ∑ h1, ∑ h1', (w2 h0 h0' h1 h1' : ℂ) * X h0 h0' h1 h1'‖ ≤ 2 * √ε := by
    refine (norm_sum4_sub_le _ _ X hX1).trans ?_
    have e : ∀ h0 h0' h1 h1', |w1 h0 h0' h1 h1' - w2 h0 h0' h1 h1'| =
        s (h0 + h1) * s (h0 + h1') *
          (P1 h1 * P1 h1' * |P0 h0' - s (h0' + h1) * s (h0' + h1')|) := by
      intro h0 h0' h1 h1'
      rw [show w1 h0 h0' h1 h1' - w2 h0 h0' h1 h1' =
        (s (h0 + h1) * s (h0 + h1') * (P1 h1 * P1 h1')) *
          (P0 h0' - s (h0' + h1) * s (h0' + h1')) by rw [hw1, hw2]; ring,
        abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg (hs0 _) (hs0 _))
          (mul_nonneg (hP1 _) (hP1 _)))]
      ring
    simp_rw [e]
    rw [sum4_perm2]
    calc ∑ h1, ∑ h1', ∑ h0, ∑ h0', s (h0 + h1) * s (h0 + h1') *
          (P1 h1 * P1 h1' * |P0 h0' - s (h0' + h1) * s (h0' + h1')|)
        = ∑ h1, ∑ h1', (∑ h0, s (h0 + h1) * s (h0 + h1')) *
          (P1 h1 * P1 h1' * ∑ h0', |P0 h0' - s (h0' + h1) * s (h0' + h1')|) := by
          refine sum_congr rfl fun h1 _ => sum_congr rfl fun h1' _ => ?_
          rw [sum_mul]; refine sum_congr rfl fun h0 _ => ?_
          rw [mul_sum, mul_sum]
      _ ≤ ∑ h1, ∑ h1', 1 * (P1 h1 * P1 h1' * (2 * √ε)) := by
          refine sum_le_sum fun h1 _ => sum_le_sum fun h1' _ => ?_
          exact mul_le_mul (sum_sqrt_mul_sqrt_le hP0 hP0s h1 h1')
            (sum_abs_sub_le_two_sqrt hP0 hP0s hP1 hTV h1 h1')
            (mul_nonneg (mul_nonneg (hP1 _) (hP1 _)) (sum_nonneg fun _ _ => abs_nonneg _))
            zero_le_one
      _ = 2 * √ε := by
          simp_rw [one_mul, ← sum_mul, ← mul_sum, hP1s, ← sum_mul, hP1s]; ring
  have step3 : (∑ h0, ∑ h0', ∑ h1, ∑ h1', (w2 h0 h0' h1 h1' : ℂ) * X h0 h0' h1 h1') =
      ((∑ h1, ∑ h1', P1 h1 * P1 h1' *
        ‖∑ h, (f (h + h1) * (√(P0 (h + h1)) : ℂ)) *
          conj (f (h + h1') * (√(P0 (h + h1')) : ℂ))‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum4_perm2, Complex.ofReal_sum]
    refine sum_congr rfl fun h1 _ => ?_
    rw [Complex.ofReal_sum]
    refine sum_congr rfl fun h1' _ => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_mul, ofReal_norm_sq, map_sum, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun h0 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h0' _ => ?_
    simp only [hw2, hX, hs, map_mul, Complex.conj_ofReal, RCLike.conj_conj]
    push_cast
    ring
  have e0 : (∑ h0, ∑ h0', ∑ h1, ∑ h1', ((P0 h0 * P0 h0' * P1 h1 * P1 h1' : ℝ) : ℂ) *
      (f (h0 + h1) * conj (f (h0 + h1')) * conj (f (h0' + h1)) * f (h0' + h1'))) =
      ∑ h0, ∑ h0', ∑ h1, ∑ h1', ((P0 h0 * P0 h0' * P1 h1 * P1 h1' : ℝ) : ℂ) * X h0 h0' h1 h1' :=
    rfl
  rw [e0, ← step3]
  refine (norm_sub_le_norm_sub_add_norm_sub _
    (∑ h0, ∑ h0', ∑ h1, ∑ h1', (w1 h0 h0' h1 h1' : ℂ) * X h0 h0' h1 h1') _).trans ?_
  linarith

include hP0 hP0s hP1 hP1s hTV in
/-- **Local inverse `U²` theorem** (Green–Tao, Theorem 4.10), general form. -/
theorem loc_u2 {η : ℝ} (hεη : 144 * ε ≤ η ^ 2) (hη : 0 ≤ η)
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (h : η ≤ ‖∑ h0, ∑ h0', ∑ h1, ∑ h1', ((P0 h0 * P0 h0' * P1 h1 * P1 h1' : ℝ) : ℂ) *
      (f (h0 + h1) * conj (f (h0 + h1')) * conj (f (h0' + h1)) * f (h0' + h1'))‖) :
    ∃ ξ, η / 2 ≤ ∑ n0, P0 n0 * ‖∑ n1, (P1 n1 : ℂ) * f (n0 + n1) * ech (-(ξ * n1))‖ ^ 2 := by
  set f0 : ZMod N → ℂ := fun x => f x * (√(P0 x) : ℂ) with hf0
  set R : ℝ := ∑ h1, ∑ h1', P1 h1 * P1 h1' *
    ‖∑ h, (f (h + h1) * (√(P0 (h + h1)) : ℂ)) * conj (f (h + h1') * (√(P0 (h + h1')) : ℂ))‖ ^ 2
    with hR
  have hrep := u2_replace hP0 hP0s hP1 hP1s hTV f hf
  rw [← hR] at hrep
  have hR0 : 0 ≤ R := sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (hP1 _) (hP1 _)) (sq_nonneg _)
  have hRη : η - 4 * √ε ≤ R := by
    have := norm_sub_norm_le (∑ h0, ∑ h0', ∑ h1, ∑ h1', ((P0 h0 * P0 h0' * P1 h1 * P1 h1' : ℝ) : ℂ) *
      (f (h0 + h1) * conj (f (h0 + h1')) * conj (f (h0' + h1)) * f (h0' + h1'))) (R : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0] at this
    linarith
  -- Fourier: `R` is an average of `u2A` against the Parseval weights
  obtain ⟨ξ, -, hξ⟩ := exists_max_image univ (u2A P1 f0) univ_nonempty
  have hRA : R ≤ u2A P1 f0 ξ := by
    have hid := u2_identity P1 f0
    have hRe : R = ∑ a, ∑ b, P1 a * P1 b * ‖∑ h, f0 (h + a) * conj (f0 (h + b))‖ ^ 2 := rfl
    rw [hRe, hid]
    have hpar := parseval_c f0
    have hf0 : ∑ x, ‖f0 x‖ ^ 2 ≤ 1 := by
      calc ∑ x, ‖f0 x‖ ^ 2 ≤ ∑ x, P0 x := sum_le_sum fun x _ => by
            rw [hf0]; (try dsimp only)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hP0 x)]
            exact mul_le_of_le_one_left (hP0 x) (pow_le_one₀ (norm_nonneg _) (hf x))
        _ = 1 := hP0s
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    calc (1 / N : ℝ) * ∑ ξ', ‖cft f0 ξ'‖ ^ 2 * u2A P1 f0 ξ'
        ≤ (1 / N : ℝ) * ∑ ξ', ‖cft f0 ξ'‖ ^ 2 * u2A P1 f0 ξ := by
          gcongr with ξ' _
          exact hξ ξ' (mem_univ _)
      _ = (∑ x, ‖f0 x‖ ^ 2) * u2A P1 f0 ξ := by rw [hpar, ← sum_mul]; ring
      _ ≤ 1 * u2A P1 f0 ξ := mul_le_mul_of_nonneg_right hf0 (u2A_nonneg _ _ _)
      _ = u2A P1 f0 ξ := one_mul _
  have hAB := u2A_le_corr hP0 hP0s hP1 hP1s hTV f hf ξ
  refine ⟨ξ, ?_⟩
  have hsq : 12 * √ε ≤ η := by
    have : √(144 * ε) ≤ √(η ^ 2) := Real.sqrt_le_sqrt hεη
    rw [Real.sqrt_sq hη, Real.sqrt_mul (by norm_num),
      show √(144 : ℝ) = 12 by rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      at this
    exact this
  have : u2A P1 f0 ξ = u2A P1 (fun x => f x * (√(P0 x) : ℂ)) ξ := rfl
  linarith

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

lemma mem_bohr_snorm (h : ZMod N) : h ∈ bohr S (snorm S h) := by
  rw [mem_bohr_iff_snorm (snorm_nonneg h)]

lemma snorm_le_of_mem {h : ZMod N} {ρ : ℝ} (hh : h ∈ bohr S ρ) (hρ : 0 ≤ ρ) : snorm S h ≤ ρ :=
  (mem_bohr_iff_snorm hρ).mp hh

lemma snorm_add_le (h k : ZMod N) : snorm S (h + k) ≤ snorm S h + snorm S k := by
  rw [snorm_le_iff (add_nonneg (snorm_nonneg _) (snorm_nonneg _))]
  intro s hs
  rw [mul_add]
  exact (cn_add_le _ _).trans (add_le_add (cn_le_snorm hs h) (cn_le_snorm hs k))

@[simp] lemma snorm_neg (h : ZMod N) : snorm S (-h) = snorm S h := by
  unfold snorm; simp [mul_neg, cn_neg]

lemma snorm_sub_le (h k : ZMod N) : snorm S (h - k) ≤ snorm S h + snorm S k := by
  rw [sub_eq_add_neg]; exact (snorm_add_le _ _).trans (by rw [snorm_neg])

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

/-- **Local inverse `U²` theorem for Bohr sets** (Green–Tao, Theorem 4.10). -/
theorem loc_u2_bohr {ρ0 ρ1 η : ℝ} (hρ1 : 0 < ρ1) (h4 : 4 * ρ1 ≤ ρ0)
    (hsep : 7200 * S.card * ρ1 ≤ η ^ 2 * ρ0) (hη : 0 ≤ η) (f : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (h : η ≤ ‖∑ h0, ∑ h0', ∑ h1, ∑ h1',
      ((regP S ρ0 h0 * regP S ρ0 h0' * regP S ρ1 h1 * regP S ρ1 h1' : ℝ) : ℂ) *
      (f (h0 + h1) * conj (f (h0 + h1')) * conj (f (h0' + h1)) * f (h0' + h1'))‖) :
    ∃ ξ, η / 2 ≤ ∑ n0, regP S ρ0 n0 *
      ‖∑ n1, (regP S ρ1 n1 : ℂ) * f (n0 + n1) * ech (-(ξ * n1))‖ ^ 2 := by
  have hρ0 : 0 < ρ0 := by linarith
  refine loc_u2 (fun x => regP_nonneg S x) (sum_regP S hρ0.le) (fun x => regP_nonneg S x)
    (sum_regP S hρ1.le)
    (ε := 50 * S.card * ρ1 / ρ0) (fun b hb => ?_) ?_ hη f hf h
  · exact regP_tv subset_rfl hρ0 hρ1.le h4 (mem_bohr_of_regP_ne_zero hρ1.le hb)
  · rw [show 144 * (50 * S.card * ρ1 / ρ0) = 7200 * S.card * ρ1 / ρ0 by ring,
      div_le_iff₀ hρ0]
    exact hsep

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

section File_GT_CS
/-!
# The double Cauchy–Schwarz inequality used in Weyl differencing
-/

open Finset
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

lemma ofReal_norm_sq_wsum (c : α → ℝ) (u : α → ℂ) :
    ((‖∑ i, (c i : ℂ) * u i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * (u i * conj (u j)) := by
  rw [ofReal_norm_sq, map_sum, sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [map_mul, Complex.conj_ofReal]; push_cast; ring

end

end GT
end File_GT_CS

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

/-! ### Goodness -/

namespace Good

variable {T : Finset (ZMod p)} {A A' : ℝ} {l l' : ZMod p}

lemma neg (h : Good T A l) : Good T A (-l) := fun x => by rw [neg_mul, cn_neg]; exact h x

lemma iff_neg : Good T A (-l) ↔ Good T A l :=
  ⟨fun h => by simpa using h.neg, fun h => h.neg⟩

end Good

/-- A large exponential sum over a regular Bohr distribution forces goodness
(Green–Tao, Lemma 4.? "fde"). -/
lemma good_of_large {T : Finset (ZMod p)} (hT : T.Nonempty) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hε1 : ε ≤ 1) {l : ZMod p} (h : ε ≤ ‖∑ n, (regP T r n : ℂ) * ech (l * n)‖) :
    Good T (13 * T.card / (r * ε)) l := by
  intro x
  have hcard : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
  by_cases hx : 4 * snorm T x ≤ r
  · have hsh := regP_shift (Γ := T) (Γ' := T) subset_rfl hr (snorm_nonneg x) hx
      (mem_bohr_snorm x) (B := 1) (fun n => ech (l * n)) (fun n => by rw [norm_ech])
    have e : ∑ n, (regP T r n : ℂ) * ech (l * (n + x)) - ∑ n, (regP T r n : ℂ) * ech (l * n) =
        (ech (l * x) - 1) * ∑ n, (regP T r n : ℂ) * ech (l * n) := by
      rw [sub_mul, one_mul, mul_sum]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [mul_add, ech_add]; ring
    rw [e, norm_mul, one_mul] at hsh
    have h4 := four_cn_le (l * x)
    have hZ : 0 < ‖∑ n, (regP T r n : ℂ) * ech (l * n)‖ := lt_of_lt_of_le hε h
    have h1 : 4 * cn (l * x) * ε ≤ 50 * T.card * snorm T x / r :=
      calc 4 * cn (l * x) * ε ≤ ‖ech (l * x) - 1‖ * ‖∑ n, (regP T r n : ℂ) * ech (l * n)‖ :=
            mul_le_mul h4 h hε.le (norm_nonneg _)
        _ ≤ _ := hsh
    rw [div_eq_mul_inv, mul_comm (13 * (T.card : ℝ)), mul_assoc]
    rw [le_div_iff₀ hr] at h1
    have hsn := snorm_nonneg (S := T) x
    have key : cn (l * x) * (r * ε) ≤ 13 * T.card * snorm T x := by nlinarith
    rw [mul_inv, ← mul_assoc]
    calc cn (l * x) = cn (l * x) * (r * ε) * (r⁻¹ * ε⁻¹) := by field_simp
      _ ≤ 13 * T.card * snorm T x * (r⁻¹ * ε⁻¹) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = _ := by ring
  · push_neg at hx
    have hc := cn_le_half (l * x)
    have : 1 / 2 ≤ 13 * T.card / (r * ε) * snorm T x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith

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

/-- **Box Cauchy–Schwarz** with a general kernel. -/
theorem cs_box {P : α → ℝ} {Q : β → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (hQ : ∀ y, 0 ≤ Q y) (hQ1 : ∑ y, Q y = 1) (a : α → ℂ) (b : β → ℂ)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ y, ‖b y‖ ≤ 1) (G : α → β → ℂ) :
    ‖∑ x, ∑ y, (P x : ℂ) * (Q y : ℂ) * (a x * b y * G x y)‖ ^ 4 ≤
      ∑ y, ∑ y', Q y * Q y' * ‖∑ x, (P x : ℂ) * (G x y * conj (G x y'))‖ ^ 2 := by
  set T : α → ℂ := fun x => ∑ y, (Q y : ℂ) * (b y * G x y) with hT
  have e0 : ∑ x, ∑ y, (P x : ℂ) * (Q y : ℂ) * (a x * b y * G x y) =
      ∑ x, (P x : ℂ) * (a x * T x) := by
    refine sum_congr rfl fun x _ => ?_
    rw [hT, mul_sum, mul_sum]; exact sum_congr rfl fun y _ => by ring
  have s1 : ‖∑ x, ∑ y, (P x : ℂ) * (Q y : ℂ) * (a x * b y * G x y)‖ ^ 2 ≤
      ∑ x, P x * ‖T x‖ ^ 2 := by
    rw [e0]
    refine (norm_wsum_sq_le hP hP1 _).trans (sum_le_sum fun x _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hP x)
    rw [norm_mul]
    have := ha x
    have h0 := norm_nonneg (T x)
    have : ‖a x‖ * ‖T x‖ ≤ ‖T x‖ := by nlinarith [norm_nonneg (a x)]
    exact pow_le_pow_left₀ (by positivity) this 2
  set U : β → β → ℂ := fun y y' => ∑ x, (P x : ℂ) * (G x y * conj (G x y')) with hU
  have e1 : ((∑ x, P x * ‖T x‖ ^ 2 : ℝ) : ℂ) =
      ∑ y, ∑ y', ((Q y * Q y' : ℝ) : ℂ) * ((b y * conj (b y')) * U y y') := by
    push_cast
    have : ∀ x, ((‖T x‖ ^ 2 : ℝ) : ℂ) = ∑ y, ∑ y', ((Q y * Q y' : ℝ) : ℂ) *
        ((b y * G x y) * conj (b y' * G x y')) := fun x => by
      rw [hT]; exact ofReal_norm_sq_wsum _ _
    simp_rw [← Complex.ofReal_pow, this, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y' _ => ?_
    rw [hU, mul_sum, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [map_mul]; push_cast; ring
  have hTn : 0 ≤ ∑ x, P x * ‖T x‖ ^ 2 := sum_nonneg fun x _ => mul_nonneg (hP x) (by positivity)
  have s2 : (∑ x, P x * ‖T x‖ ^ 2) ^ 2 ≤ ∑ y, ∑ y', Q y * Q y' * ‖U y y'‖ ^ 2 := by
    have hQQ := prod_dist hQ hQ1
    have e2 : (∑ x, P x * ‖T x‖ ^ 2) = ‖∑ z : β × β, ((Q z.1 * Q z.2 : ℝ) : ℂ) *
        ((b z.1 * conj (b z.2)) * U z.1 z.2)‖ := by
      rw [Fintype.sum_prod_type, ← e1, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hTn]
    rw [e2]
    refine (norm_wsum_sq_le hQQ.1 hQQ.2 _).trans ?_
    rw [Fintype.sum_prod_type]
    refine sum_le_sum fun y _ => sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (hQ y) (hQ y'))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := hb y; have := hb y'
    have hbb : ‖b y‖ * ‖b y'‖ ≤ 1 := by nlinarith [norm_nonneg (b y), norm_nonneg (b y')]
    have : ‖b y‖ * ‖b y'‖ * ‖U y y'‖ ≤ ‖U y y'‖ := by
      nlinarith [norm_nonneg (U y y'), norm_nonneg (b y), norm_nonneg (b y')]
    exact pow_le_pow_left₀ (by positivity) this 2
  calc ‖∑ x, ∑ y, (P x : ℂ) * (Q y : ℂ) * (a x * b y * G x y)‖ ^ 4 =
        (‖∑ x, ∑ y, (P x : ℂ) * (Q y : ℂ) * (a x * b y * G x y)‖ ^ 2) ^ 2 := by ring
    _ ≤ (∑ x, P x * ‖T x‖ ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) s1 2
    _ ≤ _ := s2

/-- Expansion of the right-hand side of `cs_box`. -/
lemma box_expand {P : α → ℝ} {Q : β → ℝ} (G : α → β → ℂ) :
    ((∑ y, ∑ y', Q y * Q y' * ‖∑ x, (P x : ℂ) * (G x y * conj (G x y'))‖ ^ 2 : ℝ) : ℂ) =
      ∑ y, ∑ y', ∑ x, ∑ x', ((Q y * Q y' * P x * P x' : ℝ) : ℂ) *
        (G x y * conj (G x y') * conj (G x' y) * G x' y') := by
  push_cast
  refine sum_congr rfl fun y _ => sum_congr rfl fun y' _ => ?_
  rw [← Complex.ofReal_pow, ofReal_norm_sq_wsum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  simp only [map_mul, Complex.conj_conj]; push_cast; ring

/-- Fourth-moment Hölder: `(E X)^4 ≤ E X^4`. -/
lemma pow4_wavg_le {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (X : α → ℝ) :
    (∑ x, P x * X x) ^ 4 ≤ ∑ x, P x * X x ^ 4 := by
  have h1 := sq_wavg_le X hP hP1
  have h2 := sq_wavg_le (fun x => X x ^ 2) hP hP1
  calc (∑ x, P x * X x) ^ 4 = ((∑ x, P x * X x) ^ 2) ^ 2 := by ring
    _ ≤ (∑ x, P x * X x ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ ≤ ∑ x, P x * (X x ^ 2) ^ 2 := h2
    _ = _ := sum_congr rfl fun x _ => by ring

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

/-- The multiplicative derivative `x ↦ f(x + D) \bar f(x)`. -/
def mder (f : ZMod p → ℂ) (D : ZMod p) (x : ZMod p) : ℂ := f (x + D) * conj (f x)

lemma norm_mder_le {f : ZMod p → ℂ} (hf : ∀ x, ‖f x‖ ≤ 1) (D x : ZMod p) : ‖mder f D x‖ ≤ 1 := by
  unfold mder; rw [norm_mul, Complex.norm_conj]
  have := hf (x + D); have := hf x
  nlinarith [norm_nonneg (f (x + D)), norm_nonneg (f x)]

lemma sum4_swap {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M] (F : α → α → α → α → M) :
    ∑ c, ∑ d, ∑ e, ∑ g, F c d e g = ∑ e, ∑ g, ∑ c, ∑ d, F c d e g := by
  calc ∑ c, ∑ d, ∑ e, ∑ g, F c d e g = ∑ c, ∑ e, ∑ d, ∑ g, F c d e g :=
        sum_congr rfl fun c _ => sum_comm
    _ = ∑ e, ∑ c, ∑ d, ∑ g, F c d e g := sum_comm
    _ = ∑ e, ∑ c, ∑ g, ∑ d, F c d e g :=
        sum_congr rfl fun e _ => sum_congr rfl fun c _ => sum_comm
    _ = ∑ e, ∑ g, ∑ c, ∑ d, F c d e g := sum_congr rfl fun e _ => sum_comm

lemma sum6_perm {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M]
    (F : α → α → α → α → α → α → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, F a b c d e g = ∑ e, ∑ g, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d e g := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, F a b c d e g =
        ∑ a, ∑ b, ∑ e, ∑ g, ∑ c, ∑ d, F a b c d e g :=
        sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum4_swap (F a b)
    _ = _ := sum4_swap (fun a b e g => ∑ c, ∑ d, F a b c d e g)

/-- The inner correlation `V(a, a') = E_{h₁} f_D(a + h₁) \bar f_D(a' + h₁)`. -/
def u2V (S : Finset (ZMod p)) (ρ1 : ℝ) (g : ZMod p → ℂ) (a a' : ZMod p) : ℂ :=
  ∑ h1, (regP S ρ1 h1 : ℂ) * (g (a + h1) * conj (g (a' + h1)))

/-- The real `U²`-type quantity. -/
def u2R (S : Finset (ZMod p)) (ρ0 ρ1 : ℝ) (g : ZMod p → ℂ) : ℝ :=
  ∑ h0, ∑ h0', regP S ρ0 h0 * regP S ρ0 h0' * ‖u2V S ρ1 g h0 h0'‖ ^ 2

lemma norm_u2V_le {S : Finset (ZMod p)} {ρ1 : ℝ} (hρ1 : 0 ≤ ρ1) {g : ZMod p → ℂ}
    (hg : ∀ x, ‖g x‖ ≤ 1) (a a' : ZMod p) : ‖u2V S ρ1 g a a'‖ ≤ 1 := by
  unfold u2V
  refine norm_wavg_le (fun x => regP_nonneg _ _) (sum_regP S hρ1) _ fun x _ => ?_
  rw [norm_mul, Complex.norm_conj]
  have := hg (a + x); have := hg (a' + x)
  nlinarith [norm_nonneg (g (a + x)), norm_nonneg (g (a' + x))]

lemma u2R_nonneg (S : Finset (ZMod p)) (ρ0 ρ1 : ℝ) (g : ZMod p → ℂ) : 0 ≤ u2R S ρ0 ρ1 g :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)) (sq_nonneg _)

lemma u2R_le {S : Finset (ZMod p)} {ρ0 ρ1 : ℝ} (hρ0 : 0 ≤ ρ0) (hρ1 : 0 ≤ ρ1) {g : ZMod p → ℂ}
    (hg : ∀ x, ‖g x‖ ≤ 1) : u2R S ρ0 ρ1 g ≤ 1 := by
  unfold u2R
  have hP := prod_dist (fun x => regP_nonneg S (ρ := ρ0) x) (sum_regP S hρ0)
  have := wavg_le hP.1 hP.2 (fun z : ZMod p × ZMod p => ‖u2V S ρ1 g z.1 z.2‖ ^ 2) (B := 1)
    (fun z _ => by
      have := norm_u2V_le (S := S) hρ1 hg z.1 z.2
      nlinarith [norm_nonneg (u2V S ρ1 g z.1 z.2)])
  rwa [Fintype.sum_prod_type] at this

/-- The complex four-fold average equals `u2R`. -/
lemma u2_sum_eq (S : Finset (ZMod p)) (ρ0 ρ1 : ℝ) (g : ZMod p → ℂ) :
    ∑ h0, ∑ h0', ∑ h1, ∑ h1', ((regP S ρ0 h0 * regP S ρ0 h0' * regP S ρ1 h1 * regP S ρ1 h1' : ℝ) : ℂ) *
      (g (h0 + h1) * conj (g (h0 + h1')) * conj (g (h0' + h1)) * g (h0' + h1')) =
      ((u2R S ρ0 ρ1 g : ℝ) : ℂ) := by
  unfold u2R
  push_cast
  refine sum_congr rfl fun h0 _ => sum_congr rfl fun h0' _ => ?_
  rw [← Complex.ofReal_pow]
  unfold u2V
  rw [ofReal_norm_sq_wsum, mul_sum]
  refine sum_congr rfl fun h1 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun h1' _ => ?_
  simp only [map_mul, Complex.conj_conj]; push_cast; ring

/-- Two simultaneous translations of a pair of independent regular variables (complex). -/
lemma shift_pair_c {Γ : Finset (ZMod p)} {ρ ρ' : ℝ} (hρ : 0 < ρ) (h4 : 4 * ρ' ≤ ρ) {t : ZMod p}
    (ht : snorm Γ t ≤ ρ') (Φ : ZMod p → ZMod p → ℂ) (hΦ : ∀ a b, ‖Φ a b‖ ≤ 1) :
    ‖∑ a, ∑ b, ((regP Γ ρ a * regP Γ ρ b : ℝ) : ℂ) * Φ (a + t) (b + t) -
      ∑ a, ∑ b, ((regP Γ ρ a * regP Γ ρ b : ℝ) : ℂ) * Φ a b‖ ≤ 2 * (50 * Γ.card * ρ' / ρ) := by
  have hρ' : 0 ≤ ρ' := (snorm_nonneg t).trans ht
  have htb : t ∈ bohr Γ ρ' := (mem_bohr_iff_snorm hρ').2 ht
  have hP := regP_isDist Γ hρ.le
  have e : ∀ F : ZMod p → ZMod p → ℂ, ∑ a, ∑ b, ((regP Γ ρ a * regP Γ ρ b : ℝ) : ℂ) * F a b =
      ∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * F a b := fun F => by
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun b _ => ?_
    push_cast; ring
  rw [e, e]
  have s1 : ‖∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * Φ (a + t) (b + t) -
      ∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * Φ (a + t) b‖ ≤ 50 * Γ.card * ρ' / ρ := by
    rw [← sum_sub_distrib]
    simp_rw [← mul_sub]
    refine norm_wavg_le hP.1 hP.2 _ fun a _ => ?_
    have := regP_shift (Γ := Γ) subset_rfl hρ hρ' h4 htb (fun b => Φ (a + t) b) (fun b => hΦ _ _)
    simpa using this
  have s2 : ‖∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * Φ (a + t) b -
      ∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * Φ a b‖ ≤ 50 * Γ.card * ρ' / ρ := by
    have := regP_shift (Γ := Γ) subset_rfl hρ hρ' h4 htb
      (fun a => ∑ b, (regP Γ ρ b : ℂ) * Φ a b) (B := 1)
      (fun a => norm_wavg_le hP.1 hP.2 _ fun b _ => hΦ _ _)
    simpa using this
  calc _ ≤ ‖∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * Φ (a + t) (b + t) -
      ∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * Φ (a + t) b‖ +
      ‖∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * Φ (a + t) b -
      ∑ a, (regP Γ ρ a : ℂ) * ∑ b, (regP Γ ρ b : ℂ) * Φ a b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Step 1** (Green–Tao, Theorem 9.1). -/
theorem u3_step1 {S : Finset (ZMod p)} {ρ0 ρ1 ρ2 η : ℝ} (hη : 0 < η) (hρ1 : 0 < ρ1)
    (hρ2 : 0 < ρ2) (h10 : 4 * ρ1 ≤ ρ0) (h20 : 4 * ρ2 ≤ ρ0)
    (hsep1 : 7200 * S.card * ρ1 ≤ (η / 4) ^ 2 * ρ0) (hsep2 : 100 * S.card * ρ2 ≤ η / 2 * ρ0)
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hU : η ≤ ‖u3avg S ρ0 ρ1 ρ2 f‖) :
    ∃ (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p), (∀ D ∈ Ω, D ∈ bohr S (2 * ρ2)) ∧
      η / 4 ≤ ∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' * (if h - h' ∈ Ω then 1 else 0) ∧
      ∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
        ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
          ech (-(ξ D * n1))‖ ^ 2 := by
  classical
  have hρ0 : 0 < ρ0 := by linarith
  set Φ : ZMod p → ZMod p → ZMod p → ℂ := fun D a a' =>
    ((‖u2V S ρ1 (mder f D) a a'‖ ^ 2 : ℝ) : ℂ) with hΦ
  have hΦb : ∀ D a a', ‖Φ D a a'‖ ≤ 1 := fun D a a' => by
    rw [hΦ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := norm_u2V_le (S := S) hρ1.le (norm_mder_le hf D) a a'
    nlinarith [norm_nonneg (u2V S ρ1 (mder f D) a a')]
  -- rewriting the `U³` average
  have hA : u3avg S ρ0 ρ1 ρ2 f = ∑ h2, ∑ h2', ((regP S ρ2 h2 * regP S ρ2 h2' : ℝ) : ℂ) *
      ∑ h0, ∑ h0', ((regP S ρ0 h0 * regP S ρ0 h0' : ℝ) : ℂ) * Φ (h2 - h2') (h0 + h2') (h0' + h2') := by
    unfold u3avg
    rw [sum6_perm]
    refine sum_congr rfl fun h2 _ => sum_congr rfl fun h2' _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h0 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h0' _ => ?_
    rw [hΦ]; simp only
    unfold u2V
    rw [ofReal_norm_sq_wsum, mul_sum, mul_sum]
    refine sum_congr rfl fun h1 _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun h1' _ => ?_
    unfold mder
    simp only [map_mul, Complex.conj_conj]
    have e1 : h0 + h2' + h1 + (h2 - h2') = h0 + h1 + h2 := by ring
    have e2 : h0 + h2' + h1' + (h2 - h2') = h0 + h1' + h2 := by ring
    have e3 : h0' + h2' + h1 + (h2 - h2') = h0' + h1 + h2 := by ring
    have e4 : h0' + h2' + h1' + (h2 - h2') = h0' + h1' + h2 := by ring
    have e5 : h0 + h2' + h1 = h0 + h1 + h2' := by ring
    have e6 : h0 + h2' + h1' = h0 + h1' + h2' := by ring
    have e7 : h0' + h2' + h1 = h0' + h1 + h2' := by ring
    have e8 : h0' + h2' + h1' = h0' + h1' + h2' := by ring
    rw [e1, e2, e3, e4, e5, e6, e7, e8]
    push_cast; ring
  -- removing the shifts
  set U : ZMod p → ℝ := fun D => u2R S ρ0 ρ1 (mder f D) with hU'
  have hUeq : ∀ D, ∑ h0, ∑ h0', ((regP S ρ0 h0 * regP S ρ0 h0' : ℝ) : ℂ) * Φ D h0 h0' =
      ((U D : ℝ) : ℂ) := fun D => by
    rw [hU']; unfold u2R; push_cast
    refine sum_congr rfl fun h0 _ => sum_congr rfl fun h0' _ => ?_
    rw [hΦ]; push_cast; ring
  have hP2 := prod_dist (fun x => regP_nonneg S (ρ := ρ2) x) (sum_regP S hρ2.le)
  have hshift : ‖u3avg S ρ0 ρ1 ρ2 f - ∑ h2, ∑ h2', ((regP S ρ2 h2 * regP S ρ2 h2' : ℝ) : ℂ) *
      ((U (h2 - h2') : ℝ) : ℂ)‖ ≤ 2 * (50 * S.card * ρ2 / ρ0) := by
    rw [hA]
    have e : ∑ h2, ∑ h2', ((regP S ρ2 h2 * regP S ρ2 h2' : ℝ) : ℂ) *
        ∑ h0, ∑ h0', ((regP S ρ0 h0 * regP S ρ0 h0' : ℝ) : ℂ) * Φ (h2 - h2') (h0 + h2') (h0' + h2') -
        ∑ h2, ∑ h2', ((regP S ρ2 h2 * regP S ρ2 h2' : ℝ) : ℂ) * ((U (h2 - h2') : ℝ) : ℂ) =
        ∑ z : ZMod p × ZMod p, ((regP S ρ2 z.1 * regP S ρ2 z.2 : ℝ) : ℂ) *
          (∑ h0, ∑ h0', ((regP S ρ0 h0 * regP S ρ0 h0' : ℝ) : ℂ) *
            Φ (z.1 - z.2) (h0 + z.2) (h0' + z.2) - ((U (z.1 - z.2) : ℝ) : ℂ)) := by
      rw [Fintype.sum_prod_type, ← sum_sub_distrib]
      refine sum_congr rfl fun h2 _ => ?_
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun h2' _ => by ring
    rw [e]
    refine norm_wavg_le hP2.1 hP2.2 _ fun z hz => ?_
    have hz2 : regP S ρ2 z.2 ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have hsn : snorm S z.2 ≤ ρ2 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ2.le hz2) hρ2.le
    rw [← hUeq]
    exact shift_pair_c hρ0 h20 hsn (Φ (z.1 - z.2)) (hΦb _)
  -- the real average is large
  have hlarge : η / 2 ≤ ∑ z : ZMod p × ZMod p, regP S ρ2 z.1 * regP S ρ2 z.2 * U (z.1 - z.2) := by
    have e : ∑ h2, ∑ h2', ((regP S ρ2 h2 * regP S ρ2 h2' : ℝ) : ℂ) * ((U (h2 - h2') : ℝ) : ℂ) =
        ((∑ z : ZMod p × ZMod p, regP S ρ2 z.1 * regP S ρ2 z.2 * U (z.1 - z.2) : ℝ) : ℂ) := by
      rw [Fintype.sum_prod_type]; push_cast; rfl
    rw [e] at hshift
    have h1 := norm_sub_norm_le (u3avg S ρ0 ρ1 ρ2 f)
      ((∑ z : ZMod p × ZMod p, regP S ρ2 z.1 * regP S ρ2 z.2 * U (z.1 - z.2) : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 : 2 * (50 * S.card * ρ2 / ρ0) ≤ η / 2 := by
      rw [show 2 * (50 * (S.card : ℝ) * ρ2 / ρ0) = 100 * S.card * ρ2 / ρ0 by ring,
        div_le_iff₀ hρ0]; exact hsep2
    have := le_abs_self (∑ z : ZMod p × ZMod p, regP S ρ2 z.1 * regP S ρ2 z.2 * U (z.1 - z.2))
    have h3 : |∑ z : ZMod p × ZMod p, regP S ρ2 z.1 * regP S ρ2 z.2 * U (z.1 - z.2)| =
        ∑ z : ZMod p × ZMod p, regP S ρ2 z.1 * regP S ρ2 z.2 * U (z.1 - z.2) :=
      abs_of_nonneg (sum_nonneg fun z _ => mul_nonneg (hP2.1 z) (u2R_nonneg _ _ _ _))
    linarith
  -- popularity
  have hpop := popular hP2.1 hP2.2 (fun z => U (z.1 - z.2)) (B := 1) (t := η / 4)
    (by linarith) (fun z => u2R_le hρ0.le hρ1.le (norm_mder_le hf _)) hlarge
  set Ω : Finset (ZMod p) := (bohr S (2 * ρ2)).filter (fun D => η / 4 ≤ U D) with hΩ
  have hmem : ∀ D ∈ Ω, D ∈ bohr S (2 * ρ2) ∧ η / 4 ≤ U D := fun D hD => by
    rw [hΩ, mem_filter] at hD; exact hD
  have hex : ∀ D ∈ Ω, ∃ ξ : ZMod p, η / 4 / 2 ≤ ∑ n0, regP S ρ0 n0 *
      ‖∑ n1, (regP S ρ1 n1 : ℂ) * mder f D (n0 + n1) * ech (-(ξ * n1))‖ ^ 2 := by
    intro D hD
    refine loc_u2_bohr hρ1 h10 hsep1 (by linarith) (mder f D) (norm_mder_le hf D) ?_
    rw [u2_sum_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (u2R_nonneg _ _ _ _)]
    exact (hmem D hD).2
  set ξ : ZMod p → ZMod p := fun D => if hD : D ∈ Ω then (hex D hD).choose else 0 with hξ
  refine ⟨Ω, ξ, fun D hD => (hmem D hD).1, ?_, fun D hD => ?_⟩
  · have e : ∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' * (if h - h' ∈ Ω then 1 else 0) =
        ∑ z : ZMod p × ZMod p, regP S ρ2 z.1 * regP S ρ2 z.2 *
          (if η / 4 ≤ U (z.1 - z.2) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun h _ => sum_congr rfl fun h' _ => ?_
      by_cases hh : regP S ρ2 h = 0
      · simp [hh]
      by_cases hh' : regP S ρ2 h' = 0
      · simp [hh']
      congr 1
      have hb : h - h' ∈ bohr S (2 * ρ2) := by
        have := sub_mem_bohr (mem_bohr_of_regP_ne_zero hρ2.le hh)
          (mem_bohr_of_regP_ne_zero hρ2.le hh')
        rwa [two_mul]
      simp only [hΩ, mem_filter, hb, true_and]
    rw [e]; linarith
  · have := (hex D hD).choose_spec
    simp only [hξ, dif_pos hD]
    unfold mder at this
    have e : η / 4 / 2 = η / 8 := by ring
    rw [← e]; exact this

end

end GT
end File_GT_U3S1

section File_GT_U3S2
/-!
# Local inverse `U³`, second step: `ξ` respects many additive quadruples

(Green–Tao, Theorem 9.2 and Corollary 9.3.)
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma exists_unit_mul (z : ℂ) : ∃ u : ℂ, ‖u‖ ≤ 1 ∧ u * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨0, by simp, by simp [hz]⟩
  · have hn : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hz
    refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self hn]
    · rw [div_mul_eq_mul_div, mul_comm (conj z), Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp

/-- The additive quadruple built from `h, h', k, k'`. -/
def quad4 (h h' k k' : ZMod p) : Fin 4 → ZMod p := ![h - h', k - k', h - k', k - h']

lemma ech_four (a b c d : ZMod p) (n : ZMod p) :
    ech (-(a * n)) * ech (b * n) * ech (c * n) * ech (-(d * n)) = ech (-((a - b - c + d) * n)) := by
  rw [← ech_add, ← ech_add, ← ech_add]; congr 1; ring

set_option maxHeartbeats 2000000 in
open Classical in
/-- **Step 2** (Green–Tao, Theorem 9.2): many quadruples lie in `Ω⁴` and are respected by `ξ`. -/
theorem u3_step2a {S : Finset (ZMod p)} (hS : S.Nonempty) {ρ0 ρ1 ρ2 η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (hρ0 : 0 < ρ0) (hρ1 : 0 < ρ1) (hρ2 : 0 ≤ ρ2) (h21 : 4 * ρ2 ≤ ρ1)
    (hsep : 50 * S.card * ρ2 / ρ1 ≤ η ^ 2 / 64)
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p)
    (hΩ1 : η / 4 ≤ ∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' * (if h - h' ∈ Ω then 1 else 0))
    (hΩ2 : ∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
        ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
          ech (-(ξ D * n1))‖ ^ 2) :
    η ^ 8 / 2 ^ 25 ≤ ∑ h', ∑ k', ∑ h, ∑ k, regP S ρ2 h' * regP S ρ2 k' * regP S ρ2 h *
      regP S ρ2 k * (if (∀ i, quad4 h h' k k' i ∈ Ω) ∧
        Good S (13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25))) (sig ξ (quad4 h h' k k')) then 1 else 0) := by
  classical
  have hP0 := regP_isDist S hρ0.le
  have hP1 := regP_isDist S hρ1.le
  have hP2 := regP_isDist S hρ2
  have hq4 : ∀ a b c d, 0 ≤ regP S ρ2 a * regP S ρ2 b * regP S ρ2 c * regP S ρ2 d :=
    fun a b c d => mul_nonneg (mul_nonneg (mul_nonneg (hP2.1 _) (hP2.1 _)) (hP2.1 _)) (hP2.1 _)
  set A : ZMod p → ZMod p → ℂ := fun n0 D => ∑ n1, (regP S ρ1 n1 : ℂ) *
    (f (n0 + n1 + D) * conj (f (n0 + n1))) * ech (-(ξ D * n1)) with hA
  have hA1 : ∀ n0 D, ‖A n0 D‖ ≤ 1 := fun n0 D => by
    rw [hA]
    have := norm_wavg_le hP1.1 hP1.2 (fun n1 => (f (n0 + n1 + D) * conj (f (n0 + n1))) *
      ech (-(ξ D * n1))) (B := 1) (fun n1 _ => by
        rw [norm_mul, norm_ech, mul_one, norm_mul, Complex.norm_conj]
        have := hf (n0 + n1 + D); have := hf (n0 + n1)
        nlinarith [norm_nonneg (f (n0 + n1 + D)), norm_nonneg (f (n0 + n1))])
    simpa only [mul_assoc] using this
  -- (a) pigeonholing `n0`
  have h2a : η ^ 2 / 32 ≤ ∑ n0, regP S ρ0 n0 * ∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' *
      (if h - h' ∈ Ω then ‖A n0 (h - h')‖ else 0) := by
    have hD : ∀ D, η / 8 * (if D ∈ Ω then 1 else 0) ≤
        ∑ n0, regP S ρ0 n0 * (if D ∈ Ω then ‖A n0 D‖ else 0) := by
      intro D
      by_cases hDΩ : D ∈ Ω
      · simp only [if_pos hDΩ, mul_one]
        refine (hΩ2 D hDΩ).trans (sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left ?_ (hP0.1 n0))
        have := hA1 n0 D
        have h0 := norm_nonneg (A n0 D)
        change ‖A n0 D‖ ^ 2 ≤ ‖A n0 D‖
        nlinarith
      · simp [hDΩ]
    calc η ^ 2 / 32 = η / 8 * (η / 4) := by ring
      _ ≤ η / 8 * ∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' * (if h - h' ∈ Ω then 1 else 0) :=
          mul_le_mul_of_nonneg_left hΩ1 (by positivity)
      _ = ∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' * (η / 8 * (if h - h' ∈ Ω then 1 else 0)) := by
          rw [mul_sum]; refine sum_congr rfl fun h _ => ?_
          rw [mul_sum]; exact sum_congr rfl fun h' _ => by ring
      _ ≤ ∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' *
            ∑ n0, regP S ρ0 n0 * (if h - h' ∈ Ω then ‖A n0 (h - h')‖ else 0) :=
          sum_le_sum fun h _ => sum_le_sum fun h' _ =>
            mul_le_mul_of_nonneg_left (hD _) (mul_nonneg (hP2.1 _) (hP2.1 _))
      _ = _ := by
          simp_rw [mul_sum]
          conv_rhs => rw [sum_comm]
          refine sum_congr rfl fun h _ => ?_
          conv_rhs => rw [sum_comm]
          exact sum_congr rfl fun h' _ => sum_congr rfl fun n0 _ => by ring
  obtain ⟨n0, -, hn0⟩ := exists_pos_ge hP0.1 hP0.2 _ h2a
  -- (b) phases
  choose u hu1 hu using fun D => exists_unit_mul (A n0 D)
  set F : ZMod p → ℂ := fun D => if D ∈ Ω then u D else 0 with hF
  have hF1 : ∀ D, ‖F D‖ ≤ if D ∈ Ω then 1 else 0 := fun D => by
    simp only [hF]; split_ifs
    · exact hu1 D
    · simp
  have hZ : ((∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' *
      (if h - h' ∈ Ω then ‖A n0 (h - h')‖ else 0) : ℝ) : ℂ) =
      ∑ h, ∑ h', ((regP S ρ2 h * regP S ρ2 h' : ℝ) : ℂ) * (F (h - h') * A n0 (h - h')) := by
    push_cast
    refine sum_congr rfl fun h _ => sum_congr rfl fun h' _ => ?_
    rw [hF]; simp only
    split_ifs
    · rw [hu]
    · simp
  -- (c) shifting `n1` by `h'`
  set Z' : ℂ := ∑ h, ∑ h', ((regP S ρ2 h * regP S ρ2 h' : ℝ) : ℂ) * (F (h - h') *
      ∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + h) * conj (f (n0 + n1 + h')) *
        ech (-(ξ (h - h') * (n1 + h'))))) with hZ'
  have hshift : ‖∑ h, ∑ h', ((regP S ρ2 h * regP S ρ2 h' : ℝ) : ℂ) * (F (h - h') * A n0 (h - h')) -
      Z'‖ ≤ 50 * S.card * ρ2 / ρ1 := by
    have hP22 := prod_dist hP2.1 hP2.2
    have e : ∑ h, ∑ h', ((regP S ρ2 h * regP S ρ2 h' : ℝ) : ℂ) * (F (h - h') * A n0 (h - h')) -
        Z' = ∑ z : ZMod p × ZMod p, ((regP S ρ2 z.1 * regP S ρ2 z.2 : ℝ) : ℂ) *
          (F (z.1 - z.2) * (A n0 (z.1 - z.2) - ∑ n1, (regP S ρ1 n1 : ℂ) *
            (f (n0 + n1 + z.1) * conj (f (n0 + n1 + z.2)) *
              ech (-(ξ (z.1 - z.2) * (n1 + z.2)))))) := by
      rw [hZ', Fintype.sum_prod_type, ← sum_sub_distrib]
      refine sum_congr rfl fun h _ => ?_
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun h' _ => by ring
    rw [e]
    refine norm_wavg_le hP22.1 hP22.2 _ fun z hz => ?_
    have hz2 : regP S ρ2 z.2 ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have hsn : snorm S z.2 ≤ ρ2 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ2 hz2) hρ2
    rw [norm_mul]
    have hFz : ‖F (z.1 - z.2)‖ ≤ 1 := (hF1 _).trans (by split_ifs <;> norm_num)
    have hsh := regP_shift (Γ := S) subset_rfl hρ1 hρ2 h21 ((mem_bohr_iff_snorm hρ2).2 hsn)
      (fun n1 => f (n0 + n1 + (z.1 - z.2)) * conj (f (n0 + n1)) * ech (-(ξ (z.1 - z.2) * n1)))
      (B := 1) (fun n1 => by
        rw [norm_mul, norm_ech, mul_one, norm_mul, Complex.norm_conj]
        have := hf (n0 + n1 + (z.1 - z.2)); have := hf (n0 + n1)
        nlinarith [norm_nonneg (f (n0 + n1 + (z.1 - z.2))), norm_nonneg (f (n0 + n1))])
    have e2 : ∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + (n1 + z.2) + (z.1 - z.2)) *
        conj (f (n0 + (n1 + z.2))) * ech (-(ξ (z.1 - z.2) * (n1 + z.2)))) =
        ∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + z.1) * conj (f (n0 + n1 + z.2)) *
          ech (-(ξ (z.1 - z.2) * (n1 + z.2)))) := by
      refine sum_congr rfl fun n1 _ => ?_
      have e3 : n0 + (n1 + z.2) + (z.1 - z.2) = n0 + n1 + z.1 := by ring
      have e4 : n0 + (n1 + z.2) = n0 + n1 + z.2 := by ring
      rw [e3, e4]
    rw [e2] at hsh
    have e5 : A n0 (z.1 - z.2) = ∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + (z.1 - z.2)) *
        conj (f (n0 + n1)) * ech (-(ξ (z.1 - z.2) * n1))) := by
      rw [hA]; exact sum_congr rfl fun n1 _ => by ring
    rw [e5, norm_sub_rev]
    rw [one_mul] at hsh
    calc ‖F (z.1 - z.2)‖ * ‖_‖ ≤ 1 * (50 * S.card * ρ2 / ρ1) :=
          mul_le_mul hFz hsh (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hZ'big : η ^ 2 / 64 ≤ ‖Z'‖ := by
    have h1 := norm_sub_norm_le (∑ h, ∑ h', ((regP S ρ2 h * regP S ρ2 h' : ℝ) : ℂ) *
      (F (h - h') * A n0 (h - h'))) Z'
    rw [← hZ, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 := le_abs_self (∑ h, ∑ h', regP S ρ2 h * regP S ρ2 h' *
      (if h - h' ∈ Ω then ‖A n0 (h - h')‖ else 0))
    rw [← hZ] at hshift
    linarith
  -- (d) Cauchy–Schwarz
  set K : ZMod p → ZMod p → ZMod p → ℂ := fun n1 h h' =>
    F (h - h') * ech (-(ξ (h - h') * (n1 + h'))) with hK
  set Y : ZMod p → ℂ := fun n1 => ∑ h, ∑ h', (regP S ρ2 h : ℂ) * (regP S ρ2 h' : ℂ) *
    (f (n0 + n1 + h) * conj (f (n0 + n1 + h')) * K n1 h h') with hY
  have hZY : Z' = ∑ n1, (regP S ρ1 n1 : ℂ) * Y n1 := by
    rw [hZ', hY]
    simp_rw [mul_sum]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun h _ => ?_
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun h' _ => ?_
    refine sum_congr rfl fun n1 _ => ?_
    rw [hK]; push_cast; ring
  set BOX : ZMod p → ℝ := fun n1 => ∑ y, ∑ y', regP S ρ2 y * regP S ρ2 y' *
    ‖∑ x, (regP S ρ2 x : ℂ) * (K n1 x y * conj (K n1 x y'))‖ ^ 2 with hBOX
  have hY4 : ∀ n1, ‖Y n1‖ ^ 4 ≤ BOX n1 := fun n1 =>
    cs_box hP2.1 hP2.2 hP2.1 hP2.2 (fun h => f (n0 + n1 + h)) (fun h' => conj (f (n0 + n1 + h')))
      (fun h => hf _) (fun h' => by rw [Complex.norm_conj]; exact hf _) (K n1)
  have hbound : (η ^ 2 / 64) ^ 4 ≤ ∑ n1, regP S ρ1 n1 * BOX n1 := by
    have h1 : ‖Z'‖ ≤ ∑ n1, regP S ρ1 n1 * ‖Y n1‖ := by
      rw [hZY]
      refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n1 _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP1.1 n1)]
    have h2 := pow4_wavg_le hP1.1 hP1.2 (fun n1 => ‖Y n1‖)
    calc (η ^ 2 / 64) ^ 4 ≤ ‖Z'‖ ^ 4 := pow_le_pow_left₀ (by positivity) hZ'big 4
      _ ≤ (∑ n1, regP S ρ1 n1 * ‖Y n1‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
      _ ≤ ∑ n1, regP S ρ1 n1 * ‖Y n1‖ ^ 4 := h2
      _ ≤ _ := sum_le_sum fun n1 _ => mul_le_mul_of_nonneg_left (hY4 n1) (hP1.1 n1)
  -- (e) expanding
  set σ : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p := fun h h' k k' =>
    sig ξ (quad4 h h' k k') with hσ
  set X : ZMod p → ZMod p → ZMod p → ZMod p → ℝ := fun h h' k k' =>
    if (∀ i, quad4 h h' k k' i ∈ Ω) then ‖∑ n1, (regP S ρ1 n1 : ℂ) * ech (-(σ h h' k k' * n1))‖
    else 0 with hX
  have hKprod : ∀ n1 h h' k k', K n1 h h' * conj (K n1 h k') * conj (K n1 k h') * K n1 k k' =
      (K 0 h h' * conj (K 0 h k') * conj (K 0 k h') * K 0 k k') * ech (-(σ h h' k k' * n1)) := by
    intro n1 h h' k k'
    have hKn : ∀ a b, K n1 a b = K 0 a b * ech (-(ξ (a - b) * n1)) := fun a b => by
      rw [hK]; simp only
      rw [mul_assoc, ← ech_add]; congr 2; ring
    rw [hKn h h', hKn h k', hKn k h', hKn k k']
    simp only [map_mul, ← ech_neg, neg_neg]
    have := ech_four (ξ (h - h')) (ξ (h - k')) (ξ (k - h')) (ξ (k - k')) n1
    have hs : σ h h' k k' = ξ (h - h') - ξ (h - k') - ξ (k - h') + ξ (k - k') := by
      rw [hσ]; simp only [sig, quad4]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring
    rw [hs, ← this]
    ring
  have hK0 : ∀ h h' k k', ‖K 0 h h' * conj (K 0 h k') * conj (K 0 k h') * K 0 k k'‖ ≤
      if (∀ i, quad4 h h' k k' i ∈ Ω) then 1 else 0 := by
    intro h h' k k'
    have hKb : ∀ a b, ‖K 0 a b‖ ≤ if a - b ∈ Ω then 1 else 0 := fun a b => by
      rw [hK]; simp only; rw [norm_mul, norm_ech, mul_one]; exact hF1 _
    simp only [norm_mul, Complex.norm_conj]
    have h1 := hKb h h'; have h2 := hKb h k'; have h3 := hKb k h'; have h4 := hKb k k'
    have hq : (∀ i, quad4 h h' k k' i ∈ Ω) ↔
        (h - h' ∈ Ω ∧ k - k' ∈ Ω ∧ h - k' ∈ Ω ∧ k - h' ∈ Ω) := by
      constructor
      · intro H; exact ⟨H 0, H 1, H 2, H 3⟩
      · rintro ⟨a, b, c, d⟩ i
        fin_cases i
        · exact a
        · exact b
        · exact c
        · exact d
    rw [if_congr hq rfl rfl]
    have n1 := norm_nonneg (K 0 h h'); have n2 := norm_nonneg (K 0 h k')
    have n3 := norm_nonneg (K 0 k h'); have n4 := norm_nonneg (K 0 k k')
    have z : ∀ a b, a - b ∉ Ω → ‖K 0 a b‖ = 0 := fun a b hab =>
      le_antisymm ((hKb a b).trans (by rw [if_neg hab])) (norm_nonneg _)
    have o : ∀ a b, ‖K 0 a b‖ ≤ 1 := fun a b => (hKb a b).trans (by split_ifs <;> norm_num)
    split_ifs with hc
    · calc ‖K 0 h h'‖ * ‖K 0 h k'‖ * ‖K 0 k h'‖ * ‖K 0 k k'‖ ≤ 1 * 1 * 1 * 1 := by
            gcongr
            · exact o _ _
            · exact o _ _
            · exact o _ _
            · exact o _ _
        _ = 1 := by norm_num
    · by_cases c1 : h - h' ∈ Ω
      · by_cases c2 : k - k' ∈ Ω
        · by_cases c3 : h - k' ∈ Ω
          · have c4 : k - h' ∉ Ω := fun c4 => hc ⟨c1, c2, c3, c4⟩
            rw [z _ _ c4]; simp
          · rw [z _ _ c3]; simp
        · rw [z _ _ c2]; simp
      · rw [z _ _ c1]; simp
  have hexp : ∑ n1, regP S ρ1 n1 * BOX n1 ≤ ∑ h', ∑ k', ∑ h, ∑ k,
      regP S ρ2 h' * regP S ρ2 k' * regP S ρ2 h * regP S ρ2 k * X h h' k k' := by
    have e1 : ((∑ n1, regP S ρ1 n1 * BOX n1 : ℝ) : ℂ) = ∑ h', ∑ k', ∑ h, ∑ k,
        ((regP S ρ2 h' * regP S ρ2 k' * regP S ρ2 h * regP S ρ2 k : ℝ) : ℂ) *
          ((K 0 h h' * conj (K 0 h k') * conj (K 0 k h') * K 0 k k') *
            ∑ n1, (regP S ρ1 n1 : ℂ) * ech (-(σ h h' k k' * n1))) := by
      push_cast
      have e2 : ∀ n1, ((BOX n1 : ℝ) : ℂ) = ∑ h', ∑ k', ∑ h, ∑ k,
          ((regP S ρ2 h' * regP S ρ2 k' * regP S ρ2 h * regP S ρ2 k : ℝ) : ℂ) *
            (K n1 h h' * conj (K n1 h k') * conj (K n1 k h') * K n1 k k') := fun n1 => by
        rw [hBOX]; exact box_expand (K n1)
      simp_rw [e2, mul_sum]
      rw [sum_comm]; refine sum_congr rfl fun h' _ => ?_
      rw [sum_comm]; refine sum_congr rfl fun k' _ => ?_
      rw [sum_comm]; refine sum_congr rfl fun h _ => ?_
      rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
      refine sum_congr rfl fun n1 _ => ?_
      rw [hKprod n1 h h' k k']; push_cast; ring
    have hBn : 0 ≤ ∑ n1, regP S ρ1 n1 * BOX n1 := sum_nonneg fun n1 _ =>
      mul_nonneg (hP1.1 n1) (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
        mul_nonneg (mul_nonneg (hP2.1 _) (hP2.1 _)) (sq_nonneg _))
    have e3 : ∑ n1, regP S ρ1 n1 * BOX n1 = ‖((∑ n1, regP S ρ1 n1 * BOX n1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hBn]
    rw [e3, e1]
    refine (norm_sum_le _ _).trans (sum_le_sum fun h' _ => (norm_sum_le _ _).trans
      (sum_le_sum fun k' _ => (norm_sum_le _ _).trans (sum_le_sum fun h _ =>
        (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_))))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hq4 _ _ _ _)]
    refine mul_le_mul_of_nonneg_left ?_ (hq4 _ _ _ _)
    rw [hX]; simp only
    have hb := hK0 h h' k k'
    split_ifs with hq
    · rw [if_pos hq] at hb
      calc _ ≤ 1 * ‖∑ n1, (regP S ρ1 n1 : ℂ) * ech (-(σ h h' k k' * n1))‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = _ := one_mul _
    · rw [if_neg hq] at hb
      have : ‖K 0 h h' * conj (K 0 h k') * conj (K 0 k h') * K 0 k k'‖ = 0 :=
        le_antisymm hb (norm_nonneg _)
      rw [this, zero_mul]
  -- (f) popularity and goodness
  set M : ℝ := (η ^ 2 / 64) ^ 4 with hM
  have hM8 : M = η ^ 8 / 2 ^ 24 := by rw [hM]; ring
  have hQ4 := fun z : ZMod p × ZMod p × ZMod p × ZMod p =>
    mul_nonneg (mul_nonneg (mul_nonneg (hP2.1 z.1) (hP2.1 z.2.1)) (hP2.1 z.2.2.1)) (hP2.1 z.2.2.2)
  have hQ41 : ∑ z : ZMod p × ZMod p × ZMod p × ZMod p,
      regP S ρ2 z.1 * regP S ρ2 z.2.1 * regP S ρ2 z.2.2.1 * regP S ρ2 z.2.2.2 = 1 := by
    simp only [Fintype.sum_prod_type]
    simp only [← sum_mul, ← mul_sum, hP2.2, one_mul, mul_one]
  have hXle : ∀ z : ZMod p × ZMod p × ZMod p × ZMod p, X z.2.2.1 z.1 z.2.2.2 z.2.1 ≤ 1 := by
    intro z; rw [hX]; simp only
    split_ifs
    · exact norm_wavg_le hP1.1 hP1.2 _ fun n1 _ => by rw [norm_ech]
    · norm_num
  have hmean : M ≤ ∑ z : ZMod p × ZMod p × ZMod p × ZMod p,
      regP S ρ2 z.1 * regP S ρ2 z.2.1 * regP S ρ2 z.2.2.1 * regP S ρ2 z.2.2.2 *
        X z.2.2.1 z.1 z.2.2.2 z.2.1 := by
    simp only [Fintype.sum_prod_type]
    exact hbound.trans hexp
  have hpop := popular hQ4 hQ41 (fun z => X z.2.2.1 z.1 z.2.2.2 z.2.1) (B := 1) (t := M / 2)
    (by rw [hM]; positivity) hXle hmean
  have htpos : 0 < M / 2 := by rw [hM]; positivity
  have hM1 : M / 2 ≤ 1 := by
    rw [hM8]
    have : η ^ 8 ≤ 1 := pow_le_one₀ hη.le hη1
    have : (0 : ℝ) < 2 ^ 24 := by positivity
    rw [div_div, div_le_one (by positivity)]
    nlinarith
  have himp : ∀ h h' k k', M / 2 ≤ X h h' k k' → (∀ i, quad4 h h' k k' i ∈ Ω) ∧
      Good S (13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25))) (sig ξ (quad4 h h' k k')) := by
    intro h h' k k' hXt
    rw [hX] at hXt; (try simp only at hXt)
    split_ifs at hXt with hq
    · refine ⟨hq, ?_⟩
      have hg := good_of_large hS hρ1 htpos hM1 (l := -σ h h' k k')
        (by simpa [neg_mul] using hXt)
      have e : M / 2 = η ^ 8 / 2 ^ 25 := by rw [hM8]; ring
      rw [e] at hg
      exact Good.iff_neg.1 hg
    · exact absurd hXt (not_le.2 htpos)
  calc η ^ 8 / 2 ^ 25 = M - M / 2 := by rw [hM8]; ring
    _ ≤ 1 * ∑ z : ZMod p × ZMod p × ZMod p × ZMod p,
          regP S ρ2 z.1 * regP S ρ2 z.2.1 * regP S ρ2 z.2.2.1 * regP S ρ2 z.2.2.2 *
            (if M / 2 ≤ X z.2.2.1 z.1 z.2.2.2 z.2.1 then 1 else 0) := hpop
    _ ≤ _ := by
        rw [one_mul]
        simp only [Fintype.sum_prod_type]
        refine sum_le_sum fun h' _ => sum_le_sum fun k' _ => sum_le_sum fun h _ =>
          sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hq4 _ _ _ _)
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd (himp h h' k k' h1) h2
        · norm_num
        · exact le_rfl

end

end GT
end File_GT_U3S2

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

lemma shift_ctx {α : Type*} [Fintype α] {μ : α → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    {Γ Γ' : Finset (ZMod p)} (hΓ : Γ ⊆ Γ') {ρ ρ' : ℝ} (hρ : 0 < ρ) (h4 : 4 * ρ' ≤ ρ)
    (s : α → ZMod p) (hs : ∀ a, μ a ≠ 0 → snorm Γ' (s a) ≤ ρ') (c : α → ZMod p) {B : ℝ}
    (G : α → ZMod p → ℝ) (hG : ∀ a x, |G a x| ≤ B) :
    |∑ a, μ a * ∑ x, regP Γ ρ (x - c a) * G a (x + s a) -
      ∑ a, μ a * ∑ x, regP Γ ρ (x - c a) * G a x| ≤ B * (50 * Γ.card * ρ' / ρ) := by
  rw [← sum_sub_distrib]
  have e : ∀ a, μ a * ∑ x, regP Γ ρ (x - c a) * G a (x + s a) -
      μ a * ∑ x, regP Γ ρ (x - c a) * G a x = μ a * (∑ x, regP Γ ρ (x - c a) * G a (x + s a) -
      ∑ x, regP Γ ρ (x - c a) * G a x) := fun a => by ring
  simp_rw [e]
  refine abs_wavg_le hμ hμ1 _ fun a ha => ?_
  exact shift_real_c hΓ hρ h4 (hs a ha) (c a) (G a) (hG a)

/-- Translating the innermost of six nested regular averages. -/
lemma shift6 {w1 w2 w3 w4 w5 : ZMod p → ℝ} (h1 : ∀ x, 0 ≤ w1 x) (h1' : ∑ x, w1 x = 1)
    (h2 : ∀ x, 0 ≤ w2 x) (h2' : ∑ x, w2 x = 1) (h3 : ∀ x, 0 ≤ w3 x) (h3' : ∑ x, w3 x = 1)
    (h4 : ∀ x, 0 ≤ w4 x) (h4' : ∑ x, w4 x = 1) (h5 : ∀ x, 0 ≤ w5 x) (h5' : ∑ x, w5 x = 1)
    {Γ Γ' : Finset (ZMod p)} (hΓ : Γ ⊆ Γ') {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ4 : 4 * ρ' ≤ ρ)
    (s : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p)
    (hs : ∀ a b c d e, w1 a * w2 b * w3 c * w4 d * w5 e ≠ 0 → snorm Γ' (s a b c d e) ≤ ρ')
    (G : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ)
    (hG : ∀ a b c d e f, |G a b c d e f| ≤ 1) :
    |∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, w1 a * w2 b * w3 c * w4 d * w5 e * regP Γ ρ f *
        G a b c d e (f + s a b c d e) -
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, w1 a * w2 b * w3 c * w4 d * w5 e * regP Γ ρ f *
        G a b c d e f| ≤ 50 * Γ.card * ρ' / ρ := by
  set μ : ZMod p × ZMod p × ZMod p × ZMod p × ZMod p → ℝ := fun z =>
    w1 z.1 * w2 z.2.1 * w3 z.2.2.1 * w4 z.2.2.2.1 * w5 z.2.2.2.2 with hμ
  have hμ0 : ∀ z, 0 ≤ μ z := fun z => by
    simp only [hμ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (h1 _) (h2 _)) (h3 _)) (h4 _)) (h5 _)
  have hμ1 : ∑ z, μ z = 1 := by
    simp only [hμ, Fintype.sum_prod_type, ← sum_mul, ← mul_sum, h1', h2', h3', h4', h5', one_mul,
      mul_one]
  have key := shift_ctx hμ0 hμ1 hΓ hρ hρ4 (fun z => s z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)
    (fun z hz => hs _ _ _ _ _ hz) (fun _ => 0)
    (fun z f => G z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 f) (fun _ _ => hG _ _ _ _ _ _)
  simp only [one_mul, sub_zero] at key
  have e : ∀ H : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ,
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, w1 a * w2 b * w3 c * w4 d * w5 e * regP Γ ρ f *
        H a b c d e f = ∑ z, μ z * ∑ f, regP Γ ρ f * H z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 f := by
    intro H
    simp only [hμ, Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
      sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [e (fun a b c d e f => G a b c d e (f + s a b c d e)), e G]
  exact key

lemma snorm_le_of_regP_ne {Γ : Finset (ZMod p)} {ρ : ℝ} (hρ : 0 ≤ ρ) {x : ZMod p}
    (hx : regP Γ ρ x ≠ 0) : snorm Γ x ≤ ρ :=
  snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ hx) hρ

/-- **Corollary 9.3** in a general form: from an average over `quad4` to a centred random
additive quadruple. -/
theorem u3_sss {S : Finset (ZMod p)} {R2 R3 R4 : ℝ} (hR2 : 0 < R2) (hR3 : 0 < R3) (hR4 : 0 < R4)
    (h43 : R4 ≤ R3) (h32 : 8 * R3 ≤ R2) (F : (Fin 4 → ZMod p) → ℝ) (hF : ∀ q, |F q| ≤ 1)
    {c0 : ℝ} (h : c0 ≤ ∑ h', ∑ k', ∑ h, ∑ k, regP S R2 h' * regP S R2 k' * regP S R2 h *
      regP S R2 k * F (quad4 h h' k k')) :
    ∃ c : Fin 4 → ZMod p, c0 - 150 * S.card * R3 / R2 ≤ qavg S R4 R3 R2 c F := by
  classical
  have hP2 := regP_isDist S hR2.le
  have hP3 := regP_isDist S hR3.le
  have hP4 := regP_isDist S hR4.le
  have T0 : ∑ h', ∑ k', ∑ h, ∑ k, regP S R2 h' * regP S R2 k' * regP S R2 h * regP S R2 k *
      F (quad4 h h' k k') =
      ∑ n21, ∑ n22, ∑ h, ∑ k, ∑ h', ∑ k', regP S R3 n21 * regP S R4 n22 * regP S R2 h *
        regP S R2 k * regP S R2 h' * regP S R2 k' * F (quad4 h h' k k') := by
    have eY : ∀ n21 n22, ∑ h, ∑ k, ∑ h', ∑ k', regP S R3 n21 * regP S R4 n22 * regP S R2 h *
        regP S R2 k * regP S R2 h' * regP S R2 k' * F (quad4 h h' k k') =
        regP S R3 n21 * (regP S R4 n22 * ∑ h, ∑ k, ∑ h', ∑ k', regP S R2 h * regP S R2 k *
          regP S R2 h' * regP S R2 k' * F (quad4 h h' k k')) := fun n21 n22 => by
      simp only [mul_sum]; refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    simp only [eY, ← mul_sum, ← sum_mul, hP3.2, hP4.2, one_mul]
    rw [sum4_perm]
    refine sum_congr rfl fun h _ => sum_congr rfl fun k _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  -- step 1: translate `k'` by `-n22`
  have B1 := shift6 hP3.1 hP3.2 hP4.1 hP4.2 hP2.1 hP2.2 hP2.1 hP2.2 hP2.1 hP2.2 (Γ := S)
    subset_rfl hR2 (ρ' := R4) (by linarith) (fun _ n22 _ _ _ => -n22)
    (fun a b c d e hx => by
      rw [snorm_neg]
      exact snorm_le_of_regP_ne hR4.le fun h0 => hx (by rw [h0]; ring))
    (fun _ _ h k h' k' => F (quad4 h h' k k')) (fun _ _ _ _ _ _ => hF _)
  -- reorder
  have R1 : ∑ n21, ∑ n22, ∑ h, ∑ k, ∑ h', ∑ k', regP S R3 n21 * regP S R4 n22 * regP S R2 h *
        regP S R2 k * regP S R2 h' * regP S R2 k' * F (quad4 h h' k (k' + -n22)) =
      ∑ n21, ∑ n22, ∑ h', ∑ k', ∑ k, ∑ h, regP S R3 n21 * regP S R4 n22 * regP S R2 h' *
        regP S R2 k' * regP S R2 k * regP S R2 h * F (quad4 h h' k (k' + -n22)) := by
    simp only [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv
      ⟨fun x => (x.1, x.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.2.1, x.2.2.1),
       fun y => (y.1, y.2.1, y.2.2.2.2.2, y.2.2.2.2.1, y.2.2.1, y.2.2.2.1),
       fun _ => rfl, fun _ => rfl⟩ _ _ (fun x => by simp only [Equiv.coe_fn_mk]; ring)
  -- step 2: translate `h` by `n21 - n22`
  have B2 := shift6 hP3.1 hP3.2 hP4.1 hP4.2 hP2.1 hP2.2 hP2.1 hP2.2 hP2.1 hP2.2 (Γ := S)
    subset_rfl hR2 (ρ' := 2 * R3) (by linarith) (fun n21 n22 _ _ _ => n21 - n22)
    (fun a b c d e hx => by
      have ha : regP S R3 a ≠ 0 := fun h0 => hx (by rw [h0]; ring)
      have hb : regP S R4 b ≠ 0 := fun h0 => hx (by rw [h0]; ring)
      have := snorm_sub_le (S := S) a b
      have := snorm_le_of_regP_ne hR3.le ha
      have := snorm_le_of_regP_ne hR4.le hb
      linarith)
    (fun n21 n22 h' k' k h => F (quad4 h h' k (k' + -n22))) (fun _ _ _ _ _ _ => hF _)
  -- the centre
  set c : ZMod p × ZMod p × ZMod p → Fin 4 → ZMod p := fun z => ![0, z.2.1 - z.2.2, z.1 - z.2.2, z.2.1]
    with hc
  have hq : ∀ n21 n22 h' k' k h, quad4 (h + (n21 - n22)) h' k (k' + -n22) =
      qd (c (h, k, k')) n22 n21 (-h') := by
    intro n21 n22 h' k' k h
    funext i
    fin_cases i <;> simp [quad4, qd, hc] <;> ring
  have R2e : ∑ n21, ∑ n22, ∑ h', ∑ k', ∑ k, ∑ h, regP S R3 n21 * regP S R4 n22 * regP S R2 h' *
        regP S R2 k' * regP S R2 k * regP S R2 h * F (quad4 (h + (n21 - n22)) h' k (k' + -n22)) =
      ∑ z : ZMod p × ZMod p × ZMod p, (regP S R2 z.1 * regP S R2 z.2.1 * regP S R2 z.2.2) *
        qavg S R4 R3 R2 (c z) F := by
    have e2 : ∀ z : ZMod p × ZMod p × ZMod p, qavg S R4 R3 R2 (c z) F =
        ∑ x2, ∑ x3, ∑ x4, regP S R4 x2 * regP S R3 x3 * regP S R2 x4 * F (qd (c z) x2 x3 (-x4)) := by
      intro z
      unfold qavg
      refine sum_congr rfl fun x2 _ => sum_congr rfl fun x3 _ => ?_
      have := sum_regP_neg_real S R2 (fun x4 => regP S R4 x2 * regP S R3 x3 * F (qd (c z) x2 x3 x4))
      (try simp only at this)
      calc ∑ x4, regP S R4 x2 * regP S R3 x3 * regP S R2 x4 * F (qd (c z) x2 x3 x4)
          = ∑ x4, regP S R2 x4 * (regP S R4 x2 * regP S R3 x3 * F (qd (c z) x2 x3 x4)) :=
            sum_congr rfl fun _ _ => by ring
        _ = ∑ x4, regP S R2 x4 * (regP S R4 x2 * regP S R3 x3 * F (qd (c z) x2 x3 (-x4))) :=
            this.symm
        _ = _ := sum_congr rfl fun _ _ => by ring
    simp only [e2, Fintype.sum_prod_type, mul_sum]
    simp only [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv
      ⟨fun x => (x.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.1, x.2.1, x.1, x.2.2.1),
       fun y => (y.2.2.2.2.1, y.2.2.2.1, y.2.2.2.2.2, y.2.2.1, y.2.1, y.1),
       fun _ => rfl, fun _ => rfl⟩ _ _ (fun x => by simp only [Equiv.coe_fn_mk, hq]; ring)
  (try simp only at B1 B2)
  have hw0 : ∀ z : ZMod p × ZMod p × ZMod p, 0 ≤ regP S R2 z.1 * regP S R2 z.2.1 * regP S R2 z.2.2 :=
    fun z => mul_nonneg (mul_nonneg (hP2.1 _) (hP2.1 _)) (hP2.1 _)
  have hw1 : ∑ z : ZMod p × ZMod p × ZMod p, regP S R2 z.1 * regP S R2 z.2.1 * regP S R2 z.2.2 = 1 := by
    simp only [Fintype.sum_prod_type, ← mul_sum, ← sum_mul, hP2.2, one_mul]
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hRR : 50 * (S.card : ℝ) * R4 / R2 ≤ 50 * S.card * R3 / R2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h43 (by positivity)) hR2.le
  have hmain : c0 - 150 * S.card * R3 / R2 ≤ ∑ z : ZMod p × ZMod p × ZMod p,
      (regP S R2 z.1 * regP S R2 z.2.1 * regP S R2 z.2.2) * qavg S R4 R3 R2 (c z) F := by
    rw [← R2e]
    have e150 : 150 * (S.card : ℝ) * R3 / R2 = 50 * S.card * R3 / R2 + 50 * S.card * (2 * R3) / R2 := by
      ring
    rw [T0] at h
    rw [R1] at B1
    have := abs_le.1 B1
    have := abs_le.1 B2
    linarith
  obtain ⟨z, -, hz⟩ := exists_pos_ge hw0 hw1 _ hmain
  exact ⟨c z, hz⟩

end

end GT
end File_GT_U3Q

section File_GT_U3Front
/-!
# Local inverse `U³`: steps one to three combined
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Steps one to three combined.** -/
theorem u3_front (hp : p.Prime) {S : Finset (ZMod p)} (hS : S.Nonempty)
    {η ρ0 ρ1 ρ2 ρ3 ρ4 ρh ρv L : ℝ} {m : ℕ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hρ0 : 0 < ρ0) (hρ1 : 0 < ρ1) (hρ2 : 0 < ρ2) (hρ3 : 0 < ρ3) (hρ4 : 0 < ρ4)
    (h10 : 4 * ρ1 ≤ ρ0) (h20 : 4 * ρ2 ≤ ρ0) (h21 : 4 * ρ2 ≤ ρ1) (h32 : 8 * ρ3 ≤ ρ2)
    (h43 : ρ4 ≤ ρ3) (hρ21 : ρ2 ≤ 1)
    (hsep1 : 7200 * S.card * ρ1 ≤ (η / 4) ^ 2 * ρ0) (hsep2 : 100 * S.card * ρ2 ≤ η / 2 * ρ0)
    (hsep3 : 50 * S.card * ρ2 / ρ1 ≤ η ^ 2 / 64)
    (hsep4 : 150 * S.card * ρ3 / ρ2 ≤ η ^ 8 / 2 ^ 26)
    (hρh : 0 < ρh) (hρv : 0 < ρv) (h2v : 2 * ρv ≤ ρh)
    (hAρ : 13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25)) * ρh ≤ 1 / 1000)
    (hAv : 13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25)) ≤ 1 / ρv)
    (hL : 1 ≤ L) (hm : 1 ≤ m) (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p)
    (he : 50 * S.card * (ρv / 2) / ρh ≤ 1 / (4 * m))
    (hmL : 16 * L ≤ 2 ^ m * (η ^ 8 / 2 ^ 26))
    (hNG : (4 * (gM m : ℝ)) ^ 3 * (1 / (p * (ρ4 / 4) ^ S.card)) ≤
      (1 / 10 ^ 6) ^ m * (η ^ 8 / 2 ^ 26) / (8 * L))
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hU : η ≤ ‖u3avg S ρ0 ρ1 ρ2 f‖) :
    ∃ (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (As : Fin 4 → Finset (ZMod p))
      (c : Fin 4 → ZMod p),
      (∀ D ∈ Ω, D ∈ bohr S (2 * ρ2)) ∧
      (∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
        ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
          ech (-(ξ D * n1))‖ ^ 2) ∧
      (∀ i, As i ⊆ Ω) ∧
      (1 / 10 ^ 6) ^ m * (η ^ 8 / 2 ^ 26) / 4 ≤ qavg S ρ4 ρ3 ρ2 c (Wt S ρv L ξ As) := by
  obtain ⟨Ω, ξ, hΩb, hΩ1, hΩ2⟩ := u3_step1 hη hρ1 hρ2 h10 h20 hsep1 hsep2 f hf hU
  have h2 := u3_step2a hS hη hη1 hρ0 hρ1 hρ2.le h21 hsep3 f hf Ω ξ hΩ1 hΩ2
  set A := 13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25)) with hA
  obtain ⟨c, hc⟩ := u3_sss hρ2 hρ3 hρ4 h43 h32
    (fun q => if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0)
    (fun q => by (try dsimp only); split_ifs <;> norm_num) h2
  have hcG : η ^ 8 / 2 ^ 26 ≤ qavg S ρ4 ρ3 ρ2 c
      (fun q => if (∀ i, q i ∈ Ω) ∧ Good S A (sig ξ q) then 1 else 0) := by
    have : η ^ 8 / 2 ^ 25 - η ^ 8 / 2 ^ 26 = η ^ 8 / 2 ^ 26 := by ring
    linarith
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨As, hAs, hW⟩ := u3_step3 hp hρ4 h43 (by linarith) hρ21 hρh hρv h2v hA0 hAρ hAv
    (by positivity) hL hm hpm he hmL hNG Ω ξ c hcG
  exact ⟨Ω, ξ, As, c, hΩb, hΩ2, hAs, hW⟩

end

end GT
end File_GT_U3Front

open Finset KM
open scoped ComplexConjugate
open Classical
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)} (hS : S.Nonempty)
    {η ρ0 ρ1 ρ2 ρ3 ρ4 ρh ρv L : ℝ} {m : ℕ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hρ0 : 0 < ρ0) (hρ1 : 0 < ρ1) (hρ2 : 0 < ρ2) (hρ3 : 0 < ρ3) (hρ4 : 0 < ρ4)
    (h10 : 4 * ρ1 ≤ ρ0) (h20 : 4 * ρ2 ≤ ρ0) (h21 : 4 * ρ2 ≤ ρ1) (h32 : 8 * ρ3 ≤ ρ2)
    (h43 : ρ4 ≤ ρ3) (hρ21 : ρ2 ≤ 1)
    (hsep1 : 7200 * S.card * ρ1 ≤ (η / 4) ^ 2 * ρ0) (hsep2 : 100 * S.card * ρ2 ≤ η / 2 * ρ0)
    (hsep3 : 50 * S.card * ρ2 / ρ1 ≤ η ^ 2 / 64)
    (hsep4 : 150 * S.card * ρ3 / ρ2 ≤ η ^ 8 / 2 ^ 26)
    (hρh : 0 < ρh) (hρv : 0 < ρv) (h2v : 2 * ρv ≤ ρh)
    (hAρ : 13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25)) * ρh ≤ 1 / 1000)
    (hAv : 13 * S.card / (ρ1 * (η ^ 8 / 2 ^ 25)) ≤ 1 / ρv)
    (hL : 1 ≤ L) (hm : 1 ≤ m) (hpm : (10 : ℝ) ^ 60 * m ^ 10 ≤ p)
    (he : 50 * S.card * (ρv / 2) / ρh ≤ 1 / (4 * m))
    (hmL : 16 * L ≤ 2 ^ m * (η ^ 8 / 2 ^ 26))
    (hNG : (4 * (gM m : ℝ)) ^ 3 * (1 / (p * (ρ4 / 4) ^ S.card)) ≤
      (1 / 10 ^ 6) ^ m * (η ^ 8 / 2 ^ 26) / (8 * L))
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hU : η ≤ ‖u3avg S ρ0 ρ1 ρ2 f‖) :
    ∃ (Ω : Finset (ZMod p)) (ξ : ZMod p → ZMod p) (As : Fin 4 → Finset (ZMod p))
      (c : Fin 4 → ZMod p),
      (∀ D ∈ Ω, D ∈ bohr S (2 * ρ2)) ∧
      (∀ D ∈ Ω, η / 8 ≤ ∑ n0, regP S ρ0 n0 *
        ‖∑ n1, (regP S ρ1 n1 : ℂ) * (f (n0 + n1 + D) * conj (f (n0 + n1))) *
          ech (-(ξ D * n1))‖ ^ 2) ∧
      (∀ i, As i ⊆ Ω) ∧
      (1 / 10 ^ 6) ^ m * (η ^ 8 / 2 ^ 26) / 4 ≤ qavg S ρ4 ρ3 ρ2 c (Wt S ρv L ξ As) :=
  @GT.u3_front p _ hp S hS η ρ0 ρ1 ρ2 ρ3 ρ4 ρh ρv L m hη hη1 hρ0 hρ1 hρ2 hρ3 hρ4 h10 h20 h21 h32 h43 hρ21 hsep1 hsep2 hsep3 hsep4 hρh hρv h2v hAρ hAv hL hm hpm he hmL hNG f hf hU

