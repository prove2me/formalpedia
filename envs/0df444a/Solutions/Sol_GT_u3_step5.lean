-- Prove2me | solution 1 for GT.u3_step5
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:47.68454+00:00
-- url     : https://prove2.me/submissions/d16569e0-69bd-4a74-9026-bf2a8f205679

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

lemma iff_neg : Good T A (-l) ↔ Good T A l :=
  ⟨fun h => by simpa using h.neg, fun h => h.neg⟩

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

/-- Markov's inequality. -/
lemma markov (X : α → ℝ) (hX : ∀ x, 0 ≤ X x) {t : ℝ} (ht : 0 < t) :
    ∑ x, P x * (if t < X x then 1 else 0) ≤ (∑ x, P x * X x) / t := by
  rw [le_div_iff₀ ht, sum_mul]
  refine sum_le_sum fun x _ => ?_
  split_ifs with h
  · nlinarith [hP x]
  · rw [mul_zero, zero_mul]; exact mul_nonneg (hP x) (hX x)

/-- Chebyshev's inequality. -/
lemma chebyshev (X : α → ℝ) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    ∑ x, P x * (if t < |X x - a| then 1 else 0) ≤ (∑ x, P x * (X x - a) ^ 2) / t ^ 2 := by
  have := markov hP (fun x => (X x - a) ^ 2) (fun x => sq_nonneg _) (pow_pos ht 2)
  refine le_trans (sum_le_sum fun x _ => ?_) this
  refine mul_le_mul_of_nonneg_left ?_ (hP x)
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    beta_reduce
    rw [← sq_abs (X x - a)]
    exact pow_lt_pow_left₀ h1 ht.le two_ne_zero
  · norm_num
  · exact le_rfl

include hP1

/-- `E|X| ≤ (E X²)^{1/2}`. -/
lemma wavg_abs_le_sqrt (X : α → ℝ) : ∑ x, P x * |X x| ≤ √(∑ x, P x * (X x) ^ 2) := by
  have h0 : 0 ≤ ∑ x, P x * |X x| := sum_nonneg fun x _ => mul_nonneg (hP x) (abs_nonneg _)
  rw [← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  have := sq_wavg_le (fun x => |X x|) hP hP1
  simpa only [sq_abs] using this

end prob

/-- A weighted average of `H` is attained or undercut at a point of positive weight. -/
lemma exists_le_ratio {α : Type*} [Fintype α] (w H : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hpos : 0 < ∑ x, w x) : ∃ x, w x ≠ 0 ∧ H x * ∑ y, w y ≤ ∑ y, w y * H y := by
  by_contra hc
  push_neg at hc
  set m := (∑ y, w y * H y) / ∑ y, w y with hm
  have hlt : ∑ y, w y * H y < ∑ y, w y * H y := by
    calc ∑ y, w y * H y = ∑ y, w y * m := by
          rw [← sum_mul, hm]; field_simp
      _ < ∑ y, w y * H y := by
          obtain ⟨x0, hx0⟩ : ∃ x, w x ≠ 0 := by
            by_contra h; push_neg at h; simp [h] at hpos
          refine sum_lt_sum (fun x _ => ?_) ⟨x0, mem_univ _, ?_⟩
          · by_cases hx : w x = 0
            · rw [hx, zero_mul, zero_mul]
            · have := hc x hx
              have hm : m < H x := by rwa [div_lt_iff₀ hpos]
              exact mul_le_mul_of_nonneg_left hm.le (hw x)
          · have := hc x0 hx0
            have hm : m < H x0 := by rwa [div_lt_iff₀ hpos]
            exact mul_lt_mul_of_pos_left hm (lt_of_le_of_ne (hw x0) (Ne.symm hx0))
  exact lt_irrefl _ hlt

/-! ### The data of the fifth step -/

/-- `1_{A₃}(a₃) 1_{A₄}(a - a₃)`. -/
def I34 (A : Fin 4 → Finset (ZMod p)) (a a3 : ZMod p) : ℝ := ind (A 2) a3 * ind (A 3) (a - a3)

lemma I12_nonneg (A : Fin 4 → Finset (ZMod p)) (a a2 : ZMod p) : 0 ≤ I12 A a a2 :=
  mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _)

lemma I12_le_one (A : Fin 4 → Finset (ZMod p)) (a a2 : ZMod p) : I12 A a a2 ≤ 1 :=
  mul_le_one₀ (ind_le_one _ _) (ind_nonneg _ _) (ind_le_one _ _)

lemma I34_nonneg (A : Fin 4 → Finset (ZMod p)) (a a3 : ZMod p) : 0 ≤ I34 A a a3 :=
  mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _)

lemma I34_le_one (A : Fin 4 → Finset (ZMod p)) (a a3 : ZMod p) : I34 A a a3 ≤ 1 :=
  mul_le_one₀ (ind_le_one _ _) (ind_nonneg _ _) (ind_le_one _ _)

omit [NeZero p] in
lemma aC_eq (c : Fin 4 → ZMod p) : aC c = cent c 2 + cent c 3 := by
  simp [aC, cent, qd]

/-- `g₃₄(a) = E 1_{A₃}(a₃) 1_{A₄}(a - a₃)`. -/
def g34 (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) (a : ZMod p) : ℝ :=
  ∑ x, regP T (R (j + 1)) x * I34 A a (cent c 2 + x)

open Classical in
lemma vb_nonneg (S : Finset (ZMod p)) (ρv : ℝ) (l : ZMod p) : 0 ≤ vb S ρv l := by
  unfold vb; split_ifs <;> norm_num

open Classical in
lemma vb_neg (S : Finset (ZMod p)) (ρv : ℝ) (l : ZMod p) : vb S ρv (-l) = vb S ρv l := by
  unfold vb; rw [Good.iff_neg]

/-- The quadruple `(a - a₂, a₂, a₃, a - a₃)`. -/
def q4 (a a2 a3 : ZMod p) : Fin 4 → ZMod p := ![a - a2, a2, a3, a - a3]

lemma Wt_q4 (S : Finset (ZMod p)) (ρv L : ℝ) (ξ : ZMod p → ZMod p) (A : Fin 4 → Finset (ZMod p))
    (a a2 a3 : ZMod p) :
    Wt S ρv L ξ A (q4 a a2 a3) =
      I12 A a a2 * I34 A a a3 * (1 - L * vb S ρv (sig ξ (q4 a a2 a3))) := by
  classical
  unfold Wt I12 I34 vb ind
  congr 1
  simp only [q4, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true]
  by_cases h0 : a - a2 ∈ A 0 <;> by_cases h1 : a2 ∈ A 1 <;> by_cases h2 : a3 ∈ A 2 <;>
    by_cases h3 : a - a3 ∈ A 3 <;> simp_all

omit [NeZero p] in
lemma sig_q4 (ξ : ZMod p → ZMod p) (a a2 a3 : ZMod p) :
    sig ξ (q4 a a2 a3) = -((ξ a3 + ξ (a - a3)) - ξ (a - a2) - ξ a2) := by
  simp only [sig, q4]; simp; ring

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

/-- Concentration of `g₃₄` (estimate (po-3)). -/
theorem g34_conc :
    ∑ a, regP T (R j) (a - aC c) *
      (g34 R A T c j a - alph R A T c j 2 * alph R A T c j 3) ^ 2 ≤
      √ε4 + 200 * T.card * θ := by
  have h := conc_po hR0 hRk hθ0 hθ1 hPR 3 (m := 1) (by decide) (by norm_num)
    (fun k => ind (A 2) (cent c 2 + k)) (fun k => by
      rw [abs_of_nonneg (ind_nonneg _ _)]; exact ind_le_one _ _)
  have e : ∀ a, g34 R A T c j a - alph R A T c j 2 * alph R A T c j 3 =
      ∑ k, regP T (R (j + 1)) k * (bal R A T c j 3 (a - cent c 2 - k) *
        ind (A 2) (cent c 2 + k)) := by
    intro a
    rw [alph_eq_sum R A T c j 2]
    simp only [g34, I34, bal, mul_sum, sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [show a - (cent c 2 + k) = a - cent c 2 - k by ring]
    have : lvl 2 = 1 := rfl
    rw [this]; ring
  simp_rw [e]
  have e2 := sum_reindex_sub T (R j) (aC c) (cent c 2) (fun n => (∑ k, regP T (R (j + 1)) k *
    (bal R A T c j 3 (n - k) * ind (A 2) (cent c 2 + k))) ^ 2)
  (try simp only at e2)
  rw [e2, show aC c - cent c 2 = cent c 3 by rw [aC_eq]; ring]
  exact h

end conc

/-- The weighted average of `W` over the quadruples `(a - a₂, a₂, a₃, a - a₃)` is close to
the average over a centred random quadruple. -/
theorem avgW_ge {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
    (hθ1 : θ ≤ 1 / 16) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (W : (Fin 4 → ZMod p) → ℝ) {B : ℝ} (hW : ∀ q, |W q| ≤ B) :
    QW R W T c j - B * (50 * T.card * θ) ≤
      ∑ a, regP T (R j) (a - aC c) * ∑ x2, regP T (R (j + 2)) x2 *
        ∑ x3, regP T (R (j + 1)) x3 * W (q4 a (cent c 1 + x2) (cent c 2 + x3)) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hW 0)
  have hP0 := regP_isDist T (hR0 j).le
  have hP1 := regP_isDist T (hR0 (j + 1)).le
  have hP2 := regP_isDist T (hR0 (j + 2)).le
  have hq : ∀ y x2 x3, q4 (aC c + y) (cent c 1 + x2) (cent c 2 + x3) = qd c x2 x3 (y + -x3) := by
    intro y x2 x3
    funext i
    fin_cases i <;> simp [q4, qd, aC, cent] <;> ring
  -- rewrite the right side
  have e : ∑ a, regP T (R j) (a - aC c) * ∑ x2, regP T (R (j + 2)) x2 *
        ∑ x3, regP T (R (j + 1)) x3 * W (q4 a (cent c 1 + x2) (cent c 2 + x3)) =
      ∑ x2, regP T (R (j + 2)) x2 * ∑ x3, regP T (R (j + 1)) x3 *
        ∑ y, regP T (R j) y * W (qd c x2 x3 (y + -x3)) := by
    rw [sum_regP_center_shift]
    simp only [hq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x2 _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun x3 _ => sum_congr rfl fun y _ => by ring
  rw [e]
  have hQW : QW R W T c j = ∑ x2, regP T (R (j + 2)) x2 * ∑ x3, regP T (R (j + 1)) x3 *
      ∑ y, regP T (R j) y * W (qd c x2 x3 y) := by
    unfold QW qavg
    refine sum_congr rfl fun x2 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun x3 _ => ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun y _ => by ring
  rw [hQW]
  have key : ∀ x2 x3, regP T (R (j + 1)) x3 ≠ 0 →
      ∑ y, regP T (R j) y * W (qd c x2 x3 y) - B * (50 * T.card * θ) ≤
        ∑ y, regP T (R j) y * W (qd c x2 x3 (y + -x3)) := by
    intro x2 x3 hx3
    have hs : snorm T (-x3) ≤ R (j + 1) := by
      rw [snorm_neg]; exact snorm_le_of_regP_ne (hR0 _).le hx3
    have h4 : 4 * R (j + 1) ≤ R j := by
      have := hRk j; nlinarith [hR0 j, hR0 (j + 1)]
    have := shift_real subset_rfl (hR0 j) h4 hs (fun y => W (qd c x2 x3 y)) (fun y => hW _)
    have h2 : B * (50 * T.card * R (j + 1) / R j) ≤ B * (50 * T.card * θ) := by
      refine mul_le_mul_of_nonneg_left ?_ hB
      rw [div_le_iff₀ (hR0 j)]
      have : (0 : ℝ) ≤ 50 * T.card := by positivity
      have := hRk j
      nlinarith
    have := (abs_le.1 this).1
    linarith
  have hsum : ∀ x2, ∑ x3, regP T (R (j + 1)) x3 * ∑ y, regP T (R j) y * W (qd c x2 x3 y) -
      B * (50 * T.card * θ) ≤ ∑ x3, regP T (R (j + 1)) x3 *
        ∑ y, regP T (R j) y * W (qd c x2 x3 (y + -x3)) := by
    intro x2
    have : ∑ x3, regP T (R (j + 1)) x3 * (∑ y, regP T (R j) y * W (qd c x2 x3 y) -
        B * (50 * T.card * θ)) ≤ ∑ x3, regP T (R (j + 1)) x3 *
        ∑ y, regP T (R j) y * W (qd c x2 x3 (y + -x3)) := by
      refine sum_le_sum fun x3 _ => ?_
      by_cases hx3 : regP T (R (j + 1)) x3 = 0
      · rw [hx3, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (key x2 x3 hx3) (hP1.1 x3)
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP1.2, one_mul] at this
    exact this
  have : ∑ x2, regP T (R (j + 2)) x2 * (∑ x3, regP T (R (j + 1)) x3 *
      ∑ y, regP T (R j) y * W (qd c x2 x3 y) - B * (50 * T.card * θ)) ≤
      ∑ x2, regP T (R (j + 2)) x2 * ∑ x3, regP T (R (j + 1)) x3 *
        ∑ y, regP T (R j) y * W (qd c x2 x3 (y + -x3)) :=
    sum_le_sum fun x2 _ => mul_le_mul_of_nonneg_left (hsum x2) (hP2.1 x2)
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP2.2, one_mul] at this
  exact this

end

end GT
end File_GT_U3S5c

section File_GT_U3S5d
/-!
# Local inverse `U³`, fifth step (Green–Tao, Theorem 9.7)
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The weight of the very bad decompositions of `a` through `a₃`. -/
def Hf (S : Finset (ZMod p)) (ρv : ℝ) (ξ : ZMod p → ZMod p) (R : ℕ → ℝ)
    (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (a a3 : ZMod p) : ℝ :=
  ∑ x2, regP T (R (j + 2)) x2 * (I12 A a (cent c 1 + x2) *
    vb S ρv (sig ξ (q4 a (cent c 1 + x2) a3)))

/-- The total weight of the very bad quadruples through `a`. -/
def hbad (S : Finset (ZMod p)) (ρv : ℝ) (ξ : ZMod p → ZMod p) (R : ℕ → ℝ)
    (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (a : ZMod p) : ℝ :=
  ∑ x3, (regP T (R (j + 1)) x3 * I34 A a (cent c 2 + x3)) *
    Hf S ρv ξ R A T c j a (cent c 2 + x3)

lemma Hf_nonneg (S : Finset (ZMod p)) (ρv : ℝ) (ξ : ZMod p → ZMod p) (R : ℕ → ℝ)
    (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (a a3 : ZMod p) : 0 ≤ Hf S ρv ξ R A T c j a a3 :=
  sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _)
    (mul_nonneg (I12_nonneg _ _ _) (vb_nonneg _ _ _))

lemma hbad_nonneg (S : Finset (ZMod p)) (ρv : ℝ) (ξ : ZMod p → ZMod p) (R : ℕ → ℝ)
    (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (a : ZMod p) : 0 ≤ hbad S ρv ξ R A T c j a :=
  sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (regP_nonneg _ _) (I34_nonneg _ _ _))
    (Hf_nonneg _ _ _ _ _ _ _ _ _ _)

/-- The inner average of `W` splits into `g₁₂ g₃₄` minus the penalty. -/
lemma innerW_eq (S : Finset (ZMod p)) (ρv L : ℝ) (ξ : ZMod p → ZMod p) (R : ℕ → ℝ)
    (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (a : ZMod p) :
    ∑ x2, regP T (R (j + 2)) x2 * ∑ x3, regP T (R (j + 1)) x3 *
        Wt S ρv L ξ A (q4 a (cent c 1 + x2) (cent c 2 + x3)) =
      g12 R A T c j a * g34 R A T c j a - L * hbad S ρv ξ R A T c j a := by
  have eh : hbad S ρv ξ R A T c j a = ∑ x2, ∑ x3, regP T (R (j + 2)) x2 *
      (regP T (R (j + 1)) x3 * (I12 A a (cent c 1 + x2) * I34 A a (cent c 2 + x3) *
        vb S ρv (sig ξ (q4 a (cent c 1 + x2) (cent c 2 + x3))))) := by
    unfold hbad Hf
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have eg : g12 R A T c j a * g34 R A T c j a = ∑ x2, ∑ x3, regP T (R (j + 2)) x2 *
      (regP T (R (j + 1)) x3 * (I12 A a (cent c 1 + x2) * I34 A a (cent c 2 + x3))) := by
    unfold g12 g34
    rw [sum_mul_sum]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [eh, eg]
  simp only [Wt_q4, mul_sum]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun x2 _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun x3 _ => ?_
  ring

/-- The very bad weight through `a₃` for the frequency `ξ'(a) = ξ(a₃) + ξ(a - a₃)`. -/
lemma Hf_eq (S : Finset (ZMod p)) (ρv : ℝ) (ξ : ZMod p → ZMod p) (R : ℕ → ℝ)
    (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (a a3 : ZMod p) :
    Hf S ρv ξ R A T c j a a3 = ∑ x2, regP T (R (j + 2)) x2 * (I12 A a (cent c 1 + x2) *
      vb S ρv ((ξ a3 + ξ (a - a3)) - ξ (a - (cent c 1 + x2)) - ξ (cent c 1 + x2))) := by
  unfold Hf
  refine sum_congr rfl fun x2 _ => ?_
  rw [sig_q4, vb_neg]

/-- A pointwise indicator estimate. -/
lemma ind3_le (x y z a b d : ℝ) :
    (if x ≤ a ∧ y ≤ b ∧ z ≤ d then (0 : ℝ) else 1) ≤
      (if a < x then 1 else 0) + (if b < y then 1 else 0) + (if d < z then 1 else 0) := by
  by_cases h0 : x ≤ a ∧ y ≤ b ∧ z ≤ d
  · rw [if_pos h0, if_neg (not_lt.2 h0.1), if_neg (not_lt.2 h0.2.1), if_neg (not_lt.2 h0.2.2)]
    norm_num
  · rw [if_neg h0]
    have : a < x ∨ b < y ∨ d < z := by
      by_contra h; push_neg at h; exact h0 ⟨h.1, h.2.1, h.2.2⟩
    rcases this with h | h | h
    · rw [if_pos h]; split_ifs <;> norm_num
    · rw [if_pos h]; split_ifs <;> norm_num
    · rw [if_pos h]; split_ifs <;> norm_num

open Classical in
/-- Choice of the frequency `ξ'` through a good `a₃`. -/
lemma xi_choice (S : Finset (ZMod p)) (ρv : ℝ) (ξ : ZMod p → ZMod p) (R : ℕ → ℝ)
    (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ) :
    ∃ ξ' : ZMod p → ZMod p, ∀ a, 0 < g34 R A T c j a →
      (∑ x2, regP T (R (j + 2)) x2 * (I12 A a (cent c 1 + x2) *
        vb S ρv (ξ' a - ξ (a - (cent c 1 + x2)) - ξ (cent c 1 + x2)))) * g34 R A T c j a ≤
        hbad S ρv ξ R A T c j a := by
  have hex : ∀ a, 0 < g34 R A T c j a → ∃ x3, regP T (R (j + 1)) x3 * I34 A a (cent c 2 + x3) ≠ 0 ∧
      Hf S ρv ξ R A T c j a (cent c 2 + x3) * g34 R A T c j a ≤ hbad S ρv ξ R A T c j a := by
    intro a ha
    exact exists_le_ratio (fun x3 => regP T (R (j + 1)) x3 * I34 A a (cent c 2 + x3))
      (fun x3 => Hf S ρv ξ R A T c j a (cent c 2 + x3))
      (fun x3 => mul_nonneg (regP_nonneg _ _) (I34_nonneg _ _ _)) ha
  refine ⟨fun a => if h : 0 < g34 R A T c j a then
    ξ (cent c 2 + Classical.choose (hex a h)) + ξ (a - (cent c 2 + Classical.choose (hex a h)))
    else 0, fun a ha => ?_⟩
  simp only [dif_pos ha]
  rw [← Hf_eq]
  exact (Classical.choose_spec (hex a ha)).2

section step5

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Theorem 9.7** (fifth step). -/
theorem u3_step5 (S : Finset (ZMod p)) (ρv L : ℝ) (ξ : ZMod p → ZMod p) {B : ℝ}
    (hWB : ∀ q, |Wt S ρv L ξ A q| ≤ B) {c4 t : ℝ} (hc4 : 0 < c4) (ht : 0 < t) (hL : 0 < L)
    (hQ : c4 ≤ QW R (Wt S ρv L ξ A) T c j) (h1 : B * (50 * T.card * θ) ≤ c4 / 2)
    (h2 : 2 * √(√ε4 + 200 * T.card * θ) ≤ c4 / 4) :
    ∃ (Gd : Finset (ZMod p)) (ξ' : ZMod p → ZMod p),
      c4 / 4 ≤ alph R A T c j 0 * alph R A T c j 1 * (alph R A T c j 2 * alph R A T c j 3) ∧
      ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) ≤
        2 / (L * t) + 1700 * (√ε4 + 200 * T.card * θ) / c4 ^ 2 ∧
      ∀ a ∈ Gd, |g12 R A T c j a - alph R A T c j 0 * alph R A T c j 1| ≤
          alph R A T c j 0 * alph R A T c j 1 / 10 ∧
        ∑ x2, regP T (R (j + 2)) x2 * (I12 A a (cent c 1 + x2) *
          vb S ρv (ξ' a - ξ (a - (cent c 1 + x2)) - ξ (cent c 1 + x2))) ≤
          2 * t * (alph R A T c j 0 * alph R A T c j 1) := by
  set α0 := alph R A T c j 0
  set α1 := alph R A T c j 1
  set α2 := alph R A T c j 2
  set α3 := alph R A T c j 3
  set δ4 := √ε4 + 200 * T.card * θ with hδ4
  have hα0 : 0 ≤ α0 := alph_nonneg R A T c j 0
  have hα1 : 0 ≤ α1 := alph_nonneg R A T c j 1
  have hα2 : 0 ≤ α2 := alph_nonneg R A T c j 2
  have hα3 : 0 ≤ α3 := alph_nonneg R A T c j 3
  have hα0' : α0 ≤ 1 := alph_le_one A T c j 0 (hR0 _).le
  have hα1' : α1 ≤ 1 := alph_le_one A T c j 1 (hR0 _).le
  have hα2' : α2 ≤ 1 := alph_le_one A T c j 2 (hR0 _).le
  have hα3' : α3 ≤ 1 := alph_le_one A T c j 3 (hR0 _).le
  have hPa := regP_center_isDist T (hR0 j).le (aC c)
  set Pa : ZMod p → ℝ := fun a => regP T (R j) (a - aC c) with hPa_def
  have hPa0 : ∀ a, 0 ≤ Pa a := hPa.1
  simp only [show ∀ a, regP T (R j) (a - aC c) = Pa a from fun _ => rfl]
  have hPa1 : ∑ a, Pa a = 1 := hPa.2
  have hg12b : ∀ a, 0 ≤ g12 R A T c j a ∧ g12 R A T c j a ≤ 1 := fun a =>
    ⟨sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _) (I12_nonneg _ _ _),
      wavg_le (regP_isDist T (hR0 _).le).1 (regP_isDist T (hR0 _).le).2 _
        fun _ _ => I12_le_one _ _ _⟩
  have hg34b : ∀ a, 0 ≤ g34 R A T c j a ∧ g34 R A T c j a ≤ 1 := fun a =>
    ⟨sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _) (I34_nonneg _ _ _),
      wavg_le (regP_isDist T (hR0 _).le).1 (regP_isDist T (hR0 _).le).2 _
        fun _ _ => I34_le_one _ _ _⟩
  -- the weighted average
  have hW := avgW_ge hR0 hRk hθ1 T c j (Wt S ρv L ξ A) hWB
  simp only [innerW_eq] at hW
  set σ := ∑ a, Pa a * (g12 R A T c j a * g34 R A T c j a) with hσ
  set Eh := ∑ a, Pa a * hbad S ρv ξ R A T c j a with hEh
  have hWs : ∑ a, Pa a * (g12 R A T c j a * g34 R A T c j a - L * hbad S ρv ξ R A T c j a) =
      σ - L * Eh := by
    simp only [hσ, hEh, mul_sub, sum_sub_distrib, mul_sum]
    congr 1; exact sum_congr rfl fun _ _ => by ring
  rw [hWs] at hW
  have hEh0 : 0 ≤ Eh := sum_nonneg fun a _ => mul_nonneg (hPa0 a) (hbad_nonneg _ _ _ _ _ _ _ _ _)
  have hσlow : c4 / 2 ≤ σ - L * Eh := by linarith
  -- concentration
  have C12 := g12_conc hR0 hRk hθ0 hθ1 hPR (A := A)
  have C34 := g34_conc hR0 hRk hθ0 hθ1 hPR (A := A)
  have hδ0 : 0 ≤ δ4 := by positivity
  have hsq : 2 * √δ4 ≤ c4 / 4 := h2
  have J12 := wavg_abs_le_sqrt hPa0 hPa1 (fun a => g12 R A T c j a - α0 * α1)
  have J34 := wavg_abs_le_sqrt hPa0 hPa1 (fun a => g34 R A T c j a - α2 * α3)
  have J12' : ∑ a, Pa a * |g12 R A T c j a - α0 * α1| ≤ √δ4 :=
    J12.trans (Real.sqrt_le_sqrt C12)
  have J34' : ∑ a, Pa a * |g34 R A T c j a - α2 * α3| ≤ √δ4 :=
    J34.trans (Real.sqrt_le_sqrt C34)
  have hsigPi : |σ - α0 * α1 * (α2 * α3)| ≤ 2 * √δ4 := by
    have e : σ - α0 * α1 * (α2 * α3) = ∑ a, Pa a * (g12 R A T c j a *
        (g34 R A T c j a - α2 * α3)) + α2 * α3 * ∑ a, Pa a * (g12 R A T c j a - α0 * α1) := by
      have hs1 : ∑ a, Pa a * (g12 R A T c j a * (g34 R A T c j a - α2 * α3)) =
          σ - α2 * α3 * ∑ a, Pa a * g12 R A T c j a := by
        rw [hσ, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun _ _ => by ring
      have hs2 : ∑ a, Pa a * (g12 R A T c j a - α0 * α1) =
          ∑ a, Pa a * g12 R A T c j a - α0 * α1 := by
        simp only [mul_sub, sum_sub_distrib, ← sum_mul, hPa1, one_mul]
      rw [hs1, hs2]; ring
    rw [e]
    have b1 : |∑ a, Pa a * (g12 R A T c j a * (g34 R A T c j a - α2 * α3))| ≤ √δ4 := by
      refine (abs_sum_le_sum_abs _ _).trans (le_trans (sum_le_sum fun a _ => ?_) J34')
      rw [abs_mul, abs_mul, abs_of_nonneg (hPa0 a), abs_of_nonneg (hg12b a).1]
      have hab := abs_nonneg (g34 R A T c j a - α2 * α3)
      exact mul_le_mul_of_nonneg_left (by nlinarith [(hg12b a).2]) (hPa0 a)
    have b2 : |α2 * α3 * ∑ a, Pa a * (g12 R A T c j a - α0 * α1)| ≤ √δ4 := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hα2 hα3)]
      have : |∑ a, Pa a * (g12 R A T c j a - α0 * α1)| ≤ √δ4 := by
        refine (abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_) J12')
        exact sum_congr rfl fun a _ => by rw [abs_mul, abs_of_nonneg (hPa0 a)]
      have hαα : α2 * α3 ≤ 1 := mul_le_one₀ hα2' hα3 hα3'
      nlinarith [abs_nonneg (∑ a, Pa a * (g12 R A T c j a - α0 * α1))]
    exact (abs_add_le _ _).trans (by linarith)
  have hLEh : 0 ≤ L * Eh := mul_nonneg hL.le hEh0
  have hPi : c4 / 4 ≤ α0 * α1 * (α2 * α3) := by
    have := (abs_le.1 hsigPi).2; linarith
  have hPipos : 0 < α0 * α1 * (α2 * α3) := by linarith
  have h01 : c4 / 4 ≤ α0 * α1 := by
    have : α2 * α3 ≤ 1 := mul_le_one₀ hα2' hα3 hα3'
    calc c4 / 4 ≤ α0 * α1 * (α2 * α3) := hPi
      _ ≤ α0 * α1 * 1 := mul_le_mul_of_nonneg_left this (mul_nonneg hα0 hα1)
      _ = α0 * α1 := mul_one _
  have h23 : c4 / 4 ≤ α2 * α3 := by
    have : α0 * α1 ≤ 1 := mul_le_one₀ hα0' hα1 hα1'
    calc c4 / 4 ≤ α0 * α1 * (α2 * α3) := hPi
      _ ≤ 1 * (α2 * α3) := mul_le_mul_of_nonneg_right this (mul_nonneg hα2 hα3)
      _ = α2 * α3 := one_mul _
  have h01p : 0 < α0 * α1 := by linarith
  have h23p : 0 < α2 * α3 := by linarith
  have C12' : ∑ a, Pa a * (g12 R A T c j a - α0 * α1) ^ 2 ≤ δ4 := C12
  have C34' : ∑ a, Pa a * (g34 R A T c j a - α2 * α3) ^ 2 ≤ δ4 := C34
  -- the good set
  set Gd := univ.filter (fun a => hbad S ρv ξ R A T c j a ≤ t * (α0 * α1 * (α2 * α3)) ∧
    |g12 R A T c j a - α0 * α1| ≤ α0 * α1 / 10 ∧ |g34 R A T c j a - α2 * α3| ≤ α2 * α3 / 2)
    with hGd
  clear_value Gd σ Eh Pa δ4 α0 α1 α2 α3
  obtain ⟨ξ', hξ'⟩ := xi_choice S ρv ξ R A T c j
  refine ⟨Gd, ξ', hPi, ?_, fun a ha => ?_⟩
  · -- the exceptional set is small
    have hpt : ∀ a, (if a ∈ Gd then (0 : ℝ) else 1) ≤
        (if t * (α0 * α1 * (α2 * α3)) < hbad S ρv ξ R A T c j a then 1 else 0) +
        (if α0 * α1 / 10 < |g12 R A T c j a - α0 * α1| then 1 else 0) +
        (if α2 * α3 / 2 < |g34 R A T c j a - α2 * α3| then 1 else 0) := by
      intro a
      simp only [hGd, mem_filter, mem_univ, true_and]
      exact ind3_le _ _ _ _ _ _
    have hM1 := markov (P := Pa) hPa0 (fun a => hbad S ρv ξ R A T c j a)
      (fun a => hbad_nonneg _ _ _ _ _ _ _ _ _) (mul_pos ht hPipos)
    have hM2 := chebyshev (P := Pa) hPa0 (fun a => g12 R A T c j a) (α0 * α1)
      (div_pos h01p (by norm_num : (0:ℝ) < 10))
    have hM3 := chebyshev (P := Pa) hPa0 (fun a => g34 R A T c j a) (α2 * α3)
      (div_pos h23p (by norm_num : (0:ℝ) < 2))
    have hsum : ∑ a, Pa a * (if a ∈ Gd then 0 else 1) ≤
        (∑ a, Pa a * hbad S ρv ξ R A T c j a) / (t * (α0 * α1 * (α2 * α3))) +
        (∑ a, Pa a * (g12 R A T c j a - α0 * α1) ^ 2) / (α0 * α1 / 10) ^ 2 +
        (∑ a, Pa a * (g34 R A T c j a - α2 * α3) ^ 2) / (α2 * α3 / 2) ^ 2 := by
      refine le_trans (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hPa0 a)) ?_
      simp only [mul_add, sum_add_distrib]
      linarith
    -- bounds on the three terms
    have t1 : Eh / (t * (α0 * α1 * (α2 * α3))) ≤ 2 / (L * t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hσle : σ ≤ 2 * (α0 * α1 * (α2 * α3)) := by
        have := (abs_le.1 hsigPi).2; linarith
      have : L * Eh ≤ σ := by linarith
      have := mul_le_mul_of_nonneg_left (this.trans hσle) ht.le
      linarith
    have t2 : (∑ a, Pa a * (g12 R A T c j a - α0 * α1) ^ 2) / (α0 * α1 / 10) ^ 2 ≤
        1600 * δ4 / c4 ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (c4 / 4) ^ 2 ≤ (α0 * α1) ^ 2 := pow_le_pow_left₀ (by linarith) h01 2
      calc (∑ a, Pa a * (g12 R A T c j a - α0 * α1) ^ 2) * c4 ^ 2 ≤ δ4 * c4 ^ 2 :=
            mul_le_mul_of_nonneg_right C12' (sq_nonneg _)
        _ ≤ δ4 * (16 * (α0 * α1) ^ 2) := mul_le_mul_of_nonneg_left (by linarith only [this]) hδ0
        _ ≤ _ := by ring_nf; rfl
    have t3 : (∑ a, Pa a * (g34 R A T c j a - α2 * α3) ^ 2) / (α2 * α3 / 2) ^ 2 ≤
        64 * δ4 / c4 ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (c4 / 4) ^ 2 ≤ (α2 * α3) ^ 2 := pow_le_pow_left₀ (by linarith) h23 2
      calc (∑ a, Pa a * (g34 R A T c j a - α2 * α3) ^ 2) * c4 ^ 2 ≤ δ4 * c4 ^ 2 :=
            mul_le_mul_of_nonneg_right C34' (sq_nonneg _)
        _ ≤ δ4 * (16 * (α2 * α3) ^ 2) := mul_le_mul_of_nonneg_left (by linarith only [this]) hδ0
        _ ≤ _ := by ring_nf; rfl
    have : 1600 * δ4 / c4 ^ 2 + 64 * δ4 / c4 ^ 2 ≤ 1700 * δ4 / c4 ^ 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith only [hδ0]) (sq_nonneg c4)
    rw [← hEh] at hsum
    linarith only [hsum, t1, t2, t3, this]
  · -- the properties at a good point
    simp only [hGd, mem_filter, mem_univ, true_and] at ha
    obtain ⟨hh, hg12, hg34⟩ := ha
    refine ⟨hg12, ?_⟩
    have hg34l : α2 * α3 / 2 ≤ g34 R A T c j a := by
      have := (abs_le.1 hg34).1; linarith only [this]
    have hg34p : 0 < g34 R A T c j a := by linarith only [hg34l, h23p]
    have hspec := hξ' a hg34p
    have hH0 : 0 ≤ ∑ x2, regP T (R (j + 2)) x2 * (I12 A a (cent c 1 + x2) *
        vb S ρv (ξ' a - ξ (a - (cent c 1 + x2)) - ξ (cent c 1 + x2))) :=
      sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _)
        (mul_nonneg (I12_nonneg _ _ _) (vb_nonneg _ _ _))
    -- Hf * g34 ≤ hbad ≤ t Π, and g34 ≥ α2α3/2
    have : (∑ x2, regP T (R (j + 2)) x2 * (I12 A a (cent c 1 + x2) *
        vb S ρv (ξ' a - ξ (a - (cent c 1 + x2)) - ξ (cent c 1 + x2)))) * (α2 * α3 / 2) ≤
        t * (α0 * α1 * (α2 * α3)) :=
      by
        have i1 := mul_le_mul_of_nonneg_left hg34l hH0
        have i2 := hspec.trans hh
        exact i1.trans i2
    have e2 : t * (α0 * α1 * (α2 * α3)) = (2 * t * (α0 * α1)) * (α2 * α3 / 2) := by ring
    rw [e2] at this
    exact le_of_mul_le_mul_right this (div_pos h23p two_pos)

end step5

end

end GT
end File_GT_U3S5d

open Finset KM
open scoped ComplexConjugate
open Classical
open GT in
theorem solution {p : ℕ} [NeZero p] {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)} {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ} (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4) (S : Finset (ZMod p)) (ρv L : ℝ) (ξ : ZMod p → ZMod p) {B : ℝ}
    (hWB : ∀ q, |Wt S ρv L ξ A q| ≤ B) {c4 t : ℝ} (hc4 : 0 < c4) (ht : 0 < t) (hL : 0 < L)
    (hQ : c4 ≤ QW R (Wt S ρv L ξ A) T c j) (h1 : B * (50 * T.card * θ) ≤ c4 / 2)
    (h2 : 2 * √(√ε4 + 200 * T.card * θ) ≤ c4 / 4) :
    ∃ (Gd : Finset (ZMod p)) (ξ' : ZMod p → ZMod p),
      c4 / 4 ≤ alph R A T c j 0 * alph R A T c j 1 * (alph R A T c j 2 * alph R A T c j 3) ∧
      ∑ a, regP T (R j) (a - aC c) * (if a ∈ Gd then 0 else 1) ≤
        2 / (L * t) + 1700 * (√ε4 + 200 * T.card * θ) / c4 ^ 2 ∧
      ∀ a ∈ Gd, |g12 R A T c j a - alph R A T c j 0 * alph R A T c j 1| ≤
          alph R A T c j 0 * alph R A T c j 1 / 10 ∧
        ∑ x2, regP T (R (j + 2)) x2 * (I12 A a (cent c 1 + x2) *
          vb S ρv (ξ' a - ξ (a - (cent c 1 + x2)) - ξ (cent c 1 + x2))) ≤
          2 * t * (alph R A T c j 0 * alph R A T c j 1) :=
  @GT.u3_step5 p _ R θ hR0 hRk hθ0 hθ1 T A c j ε4 hPR S ρv L ξ B hWB c4 t hc4 ht hL hQ h1 h2

