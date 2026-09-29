-- Prove2me | solution 1 for GT.u3_step4
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:57:01.353265+00:00
-- url     : https://prove2.me/submissions/b103152a-aa92-4875-86a0-86d0a749b874

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

@[simp] lemma snorm_zero : snorm S (0 : ZMod N) = 0 := by
  unfold snorm; split_ifs <;> simp

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

/-! ### Goodness -/

namespace Good

variable {T : Finset (ZMod p)} {A A' : ℝ} {l l' : ZMod p}

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

/-! ### A general translation estimate inside a context -/

lemma snorm_le_of_regP_ne {Γ : Finset (ZMod p)} {ρ : ℝ} (hρ : 0 ≤ ρ) {x : ZMod p}
    (hx : regP Γ ρ x ≠ 0) : snorm Γ x ≤ ρ :=
  snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ hx) hρ

end

end GT
end File_GT_U3Q

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

/-! ### Non-generic quadruples are rare -/

/-! ### Many filters -/

lemma qavg_le_one {S : Finset (ZMod p)} {r2 r3 r4 : ℝ} (hr2 : 0 ≤ r2) (hr3 : 0 ≤ r3)
    (hr4 : 0 ≤ r4) (c : Fin 4 → ZMod p) {F : (Fin 4 → ZMod p) → ℝ} (hF : ∀ q, F q ≤ 1) :
    qavg S r2 r3 r4 c F ≤ 1 := by
  have hP2 := regP_isDist S hr2
  have hP3 := regP_isDist S hr3
  have hP4 := regP_isDist S hr4
  unfold qavg
  have e : ∀ x2 x3, ∑ x4, regP S r2 x2 * regP S r3 x3 * regP S r4 x4 * F (qd c x2 x3 x4) =
      regP S r2 x2 * (regP S r3 x3 * ∑ x4, regP S r4 x4 * F (qd c x2 x3 x4)) := fun x2 x3 => by
    rw [mul_sum, mul_sum]; exact sum_congr rfl fun _ _ => by ring
  simp_rw [e, ← mul_sum]
  exact wavg_le hP2.1 hP2.2 _ fun x2 _ => wavg_le hP3.1 hP3.2 _ fun x3 _ =>
    wavg_le hP4.1 hP4.2 _ fun x4 _ => hF _

end

end GT
end File_GT_U3S3

section File_GT_U3S4a
/-!
# Local inverse `U³`, fourth step: averages over three regular variables

Tools for the energy-decrement (score maximisation) argument of Green–Tao, Theorem 9.5:
averages `avg3` over three independent regular variables, translations inside them, and the
marginal distributions of the components of a random additive quadruple.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- Average over three independent regular variables. -/
def avg3 (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (H : ZMod p → ZMod p → ZMod p → ℝ) : ℝ :=
  ∑ y2, ∑ y3, ∑ y4, regP T s2 y2 * regP T s3 y3 * regP T s4 y4 * H y2 y3 y4

lemma qavg_eq_avg3 (T : Finset (ZMod p)) (r2 r3 r4 : ℝ) (c : Fin 4 → ZMod p)
    (F : (Fin 4 → ZMod p) → ℝ) :
    qavg T r2 r3 r4 c F = avg3 T r2 r3 r4 (fun x2 x3 x4 => F (qd c x2 x3 x4)) := rfl

lemma avg3_nested (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (H : ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T s2 s3 s4 H =
      ∑ y2, regP T s2 y2 * ∑ y3, regP T s3 y3 * ∑ y4, regP T s4 y4 * H y2 y3 y4 := by
  unfold avg3
  refine sum_congr rfl fun _ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  rw [mul_sum, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma avg3_sub (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (H H' : ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T s2 s3 s4 H - avg3 T s2 s3 s4 H' = avg3 T s2 s3 s4 (fun a b c => H a b c - H' a b c) := by
  unfold avg3
  simp only [← sum_sub_distrib, mul_sub]

lemma avg3_add (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (H H' : ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T s2 s3 s4 (fun a b c => H a b c + H' a b c) = avg3 T s2 s3 s4 H + avg3 T s2 s3 s4 H' := by
  unfold avg3
  simp only [← sum_add_distrib, mul_add]

lemma avg3_smul (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (a : ℝ) (H : ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T s2 s3 s4 (fun x y z => a * H x y z) = a * avg3 T s2 s3 s4 H := by
  unfold avg3
  simp only [mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

section pos

variable {T : Finset (ZMod p)} {s2 s3 s4 : ℝ} (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4)
include hs2 hs3 hs4

lemma avg3_mono {H H' : ZMod p → ZMod p → ZMod p → ℝ} (h : ∀ a b c, H a b c ≤ H' a b c) :
    avg3 T s2 s3 s4 H ≤ avg3 T s2 s3 s4 H' :=
  sum_le_sum fun _ _ => sum_le_sum fun _ _ => sum_le_sum fun _ _ =>
    mul_le_mul_of_nonneg_left (h _ _ _) (mul_nonneg (mul_nonneg (regP_nonneg _ _)
      (regP_nonneg _ _)) (regP_nonneg _ _))

lemma avg3_const (a : ℝ) : avg3 T s2 s3 s4 (fun _ _ _ => a) = a := by
  rw [avg3_nested]
  simp only [← sum_mul, (regP_isDist T hs4).2, (regP_isDist T hs3).2, (regP_isDist T hs2).2,
    one_mul]

/-- A bounded (on the support) integrand has a bounded average. -/
lemma abs_avg3_le {H : ZMod p → ZMod p → ZMod p → ℝ} {B : ℝ}
    (hH : ∀ a b c, regP T s2 a ≠ 0 → regP T s3 b ≠ 0 → regP T s4 c ≠ 0 → |H a b c| ≤ B) :
    |avg3 T s2 s3 s4 H| ≤ B := by
  have h2 := regP_isDist T hs2
  have h3 := regP_isDist T hs3
  have h4 := regP_isDist T hs4
  rw [avg3_nested]
  exact abs_wavg_le h2.1 h2.2 _ fun a ha => abs_wavg_le h3.1 h3.2 _ fun b hb =>
    abs_wavg_le h4.1 h4.2 _ fun c hc => hH a b c ha hb hc

/-- Closeness in the innermost variable. -/
lemma avg3_close4 {H H' : ZMod p → ZMod p → ZMod p → ℝ} {e : ℝ}
    (h : ∀ a b, regP T s2 a ≠ 0 → regP T s3 b ≠ 0 →
      |∑ c, regP T s4 c * H a b c - ∑ c, regP T s4 c * H' a b c| ≤ e) :
    |avg3 T s2 s3 s4 H - avg3 T s2 s3 s4 H'| ≤ e := by
  have h2 := regP_isDist T hs2
  have h3 := regP_isDist T hs3
  have e : avg3 T s2 s3 s4 H - avg3 T s2 s3 s4 H' = ∑ a, regP T s2 a * ∑ b, regP T s3 b *
      (∑ c, regP T s4 c * H a b c - ∑ c, regP T s4 c * H' a b c) := by
    rw [avg3_nested, avg3_nested]; simp only [mul_sub, sum_sub_distrib]
  rw [e]
  exact abs_wavg_le h2.1 h2.2 _ fun a ha => abs_wavg_le h3.1 h3.2 _ fun b hb => h a b ha hb

lemma avg3_shift4 {t4 : ℝ} (hs4' : 0 < s4) (h4 : 4 * t4 ≤ s4) {a4 : ZMod p}
    (ha4 : snorm T a4 ≤ t4) {H : ZMod p → ZMod p → ZMod p → ℝ} {B : ℝ}
    (hH : ∀ a b c, |H a b c| ≤ B) :
    |avg3 T s2 s3 s4 (fun a b c => H a b (c + a4)) - avg3 T s2 s3 s4 H| ≤
      B * (50 * T.card * t4 / s4) :=
  avg3_close4 hs2 hs3 hs4 fun a b _ _ =>
    shift_real subset_rfl hs4' h4 ha4 (fun c => H a b c) (fun c => hH a b c)

end pos

lemma avg3_rot (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (H : ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T s2 s3 s4 H = avg3 T s3 s4 s2 (fun a b c => H c a b) := by
  unfold avg3
  rw [sum_comm]
  refine sum_congr rfl fun _ _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma avg3_rot' (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (H : ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T s2 s3 s4 H = avg3 T s4 s2 s3 (fun c a b => H a b c) := by
  unfold avg3
  have : ∀ y2, ∑ y3, ∑ y4, regP T s2 y2 * regP T s3 y3 * regP T s4 y4 * H y2 y3 y4 =
      ∑ y4, ∑ y3, regP T s2 y2 * regP T s3 y3 * regP T s4 y4 * H y2 y3 y4 := fun _ => sum_comm
  simp_rw [this]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- Translating all three variables. -/
lemma avg3_shift {T : Finset (ZMod p)} {s2 s3 s4 t2 t3 t4 : ℝ} (hs2 : 0 < s2) (hs3 : 0 < s3)
    (hs4 : 0 < s4) (h2 : 4 * t2 ≤ s2) (h3 : 4 * t3 ≤ s3) (h4 : 4 * t4 ≤ s4)
    {a2 a3 a4 : ZMod p} (ha2 : snorm T a2 ≤ t2) (ha3 : snorm T a3 ≤ t3) (ha4 : snorm T a4 ≤ t4)
    {H : ZMod p → ZMod p → ZMod p → ℝ} {B : ℝ} (hH : ∀ a b c, |H a b c| ≤ B) :
    |avg3 T s2 s3 s4 (fun a b c => H (a + a2) (b + a3) (c + a4)) - avg3 T s2 s3 s4 H| ≤
      B * (50 * T.card * t2 / s2 + 50 * T.card * t3 / s3 + 50 * T.card * t4 / s4) := by
  have E4 := avg3_shift4 hs2.le hs3.le hs4.le hs4 h4 ha4 (T := T)
    (H := fun a b c => H (a + a2) (b + a3) c) (fun _ _ _ => hH _ _ _)
  have E3 : |avg3 T s2 s3 s4 (fun a b c => H (a + a2) (b + a3) c) -
      avg3 T s2 s3 s4 (fun a b c => H (a + a2) b c)| ≤ B * (50 * T.card * t3 / s3) := by
    rw [avg3_rot' T s2 s3 s4 (fun a b c => H (a + a2) (b + a3) c),
      avg3_rot' T s2 s3 s4 (fun a b c => H (a + a2) b c)]
    exact avg3_shift4 hs4.le hs2.le hs3.le hs3 h3 ha3 (T := T)
      (H := fun c a b => H (a + a2) b c) (fun _ _ _ => hH _ _ _)
  have E2 : |avg3 T s2 s3 s4 (fun a b c => H (a + a2) b c) - avg3 T s2 s3 s4 H| ≤
      B * (50 * T.card * t2 / s2) := by
    rw [avg3_rot T s2 s3 s4 (fun a b c => H (a + a2) b c), avg3_rot T s2 s3 s4 H]
    exact avg3_shift4 hs3.le hs4.le hs2.le hs2 h2 ha2 (T := T)
      (H := fun b c a => H a b c) (fun _ _ _ => hH _ _ _)
  have := abs_sub_le (avg3 T s2 s3 s4 (fun a b c => H (a + a2) (b + a3) (c + a4)))
    (avg3 T s2 s3 s4 (fun a b c => H (a + a2) (b + a3) c)) (avg3 T s2 s3 s4 H)
  have := abs_sub_le (avg3 T s2 s3 s4 (fun a b c => H (a + a2) (b + a3) c))
    (avg3 T s2 s3 s4 (fun a b c => H (a + a2) b c)) (avg3 T s2 s3 s4 H)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hH 0 0 0)
  nlinarith

/-! ### Marginals of a random additive quadruple -/

/-- The scale of the `i`-th component of a random additive quadruple with scales `r2,r3,r4`. -/
def qsc (r2 r3 r4 : ℝ) : Fin 4 → ℝ := ![r4, r2, r3, r4]

lemma qd_eq_cent_add (c : Fin 4 → ZMod p) (x2 x3 x4 : ZMod p) (i : Fin 4) :
    qd c x2 x3 x4 i = cent c i + qd 0 x2 x3 x4 i := by
  fin_cases i <;> simp [qd, cent] <;> ring

lemma qd_zero_apply (x2 x3 x4 : ZMod p) :
    qd 0 x2 x3 x4 0 = x4 + (x3 - x2) ∧ qd 0 x2 x3 x4 1 = x2 ∧ qd 0 x2 x3 x4 2 = x3 ∧
      qd 0 x2 x3 x4 3 = x4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [qd] <;> ring

section marg

variable {T : Finset (ZMod p)} {s2 s3 s4 : ℝ} (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4)
include hs2 hs3 hs4

lemma avg3_only2 (F : ZMod p → ℝ) :
    avg3 T s2 s3 s4 (fun a _ _ => F a) = ∑ a, regP T s2 a * F a := by
  rw [avg3_nested]
  refine sum_congr rfl fun a _ => ?_
  simp only [← sum_mul, (regP_isDist T hs4).2, (regP_isDist T hs3).2, one_mul]

lemma avg3_only3 (F : ZMod p → ℝ) :
    avg3 T s2 s3 s4 (fun _ b _ => F b) = ∑ b, regP T s3 b * F b := by
  rw [avg3_nested]
  simp only [← sum_mul, (regP_isDist T hs4).2, one_mul, ← mul_sum, (regP_isDist T hs2).2]

lemma avg3_only4 (F : ZMod p → ℝ) :
    avg3 T s2 s3 s4 (fun _ _ c => F c) = ∑ c, regP T s4 c * F c := by
  rw [avg3_nested]
  simp only [← mul_sum, (regP_isDist T hs3).2, (regP_isDist T hs2).2, one_mul, ← sum_mul]

end marg

/-- The `i`-th component of a centred random additive quadruple is close in distribution to a
regular variable at scale `qsc r2 r3 r4 i`. -/
lemma avg3_marg {T : Finset (ZMod p)} {r2 r3 r4 : ℝ} (hr2 : 0 < r2) (hr3 : 0 < r3) (hr4 : 0 < r4)
    (h4 : 4 * (r2 + r3) ≤ r4) (F : ZMod p → ℝ) {B : ℝ} (hF : ∀ x, |F x| ≤ B) (i : Fin 4) :
    |avg3 T r2 r3 r4 (fun x2 x3 x4 => F (qd 0 x2 x3 x4 i)) -
      ∑ u, regP T (qsc r2 r3 r4 i) u * F u| ≤ B * (50 * T.card * (r2 + r3) / r4) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hF 0)
  have hE : 0 ≤ B * (50 * T.card * (r2 + r3) / r4) := by positivity
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, (qd_zero_apply _ _ _).1]
    rw [show qsc r2 r3 r4 0 = r4 from rfl, ← avg3_only4 hr2.le hr3.le hr4.le]
    refine avg3_close4 hr2.le hr3.le hr4.le fun a b ha hb => ?_
    refine shift_real subset_rfl hr4 (by linarith) ?_ F hF
    refine (snorm_sub_le _ _).trans ?_
    have := snorm_le_of_regP_ne hr2.le ha
    have := snorm_le_of_regP_ne hr3.le hb
    linarith
  · simp only [Fin.mk_one, Fin.isValue, (qd_zero_apply _ _ _).2.1]
    rw [show qsc r2 r3 r4 1 = r2 from rfl, avg3_only2 hr2.le hr3.le hr4.le, sub_self, abs_zero]
    exact hE
  · simp only [Fin.reduceFinMk, Fin.isValue, (qd_zero_apply _ _ _).2.2.1]
    rw [show qsc r2 r3 r4 2 = r3 from rfl, avg3_only3 hr2.le hr3.le hr4.le, sub_self, abs_zero]
    exact hE
  · simp only [Fin.reduceFinMk, Fin.isValue, (qd_zero_apply _ _ _).2.2.2]
    rw [show qsc r2 r3 r4 3 = r4 from rfl, avg3_only4 hr2.le hr3.le hr4.le, sub_self, abs_zero]
    exact hE

/-! ### Fubini and absorption -/

lemma avg3_eq_prod (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (H : ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T s2 s3 s4 H = ∑ v : ZMod p × ZMod p × ZMod p,
      (regP T s2 v.1 * regP T s3 v.2.1 * regP T s4 v.2.2) * H v.1 v.2.1 v.2.2 := by
  simp only [Fintype.sum_prod_type]; rfl

lemma avg3_comm (T T' : Finset (ZMod p)) (r2 r3 r4 s2 s3 s4 : ℝ)
    (K : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T r2 r3 r4 (fun a b c => avg3 T' s2 s3 s4 (fun d e f => K a b c d e f)) =
      avg3 T' s2 s3 s4 (fun d e f => avg3 T r2 r3 r4 (fun a b c => K a b c d e f)) := by
  simp only [avg3_eq_prod, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma avg3_sum_w {β : Type*} [Fintype β] (T : Finset (ZMod p)) (s2 s3 s4 : ℝ) (Q : β → ℝ)
    (K : β → ZMod p → ZMod p → ZMod p → ℝ) :
    avg3 T s2 s3 s4 (fun a b c => ∑ w, Q w * K w a b c) = ∑ w, Q w * avg3 T s2 s3 s4 (K w) := by
  simp only [avg3_eq_prod, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- **Absorption.**  An average over a random quadruple centred at `c`, perturbed by a second
random quadruple at much smaller scales `s` and by a third (arbitrarily distributed, possibly
depending on the first) perturbation at even smaller scales `t`, is close to the original
average. -/
theorem absorb {β : Type*} [Fintype β] {T : Finset (ZMod p)} {r2 r3 r4 s2 s3 s4 t2 t3 t4 : ℝ}
    (hr2 : 0 < r2) (hr3 : 0 < r3) (hr4 : 0 < r4) (hs2 : 0 < s2) (hs3 : 0 < s3) (hs4 : 0 < s4)
    (hrs2 : 4 * s2 ≤ r2) (hrs3 : 4 * s3 ≤ r3) (hrs4 : 4 * s4 ≤ r4)
    (hst2 : 4 * t2 ≤ s2) (hst3 : 4 * t3 ≤ s3) (hst4 : 4 * t4 ≤ s4)
    (Q : ZMod p → ZMod p → ZMod p → β → ℝ) (hQ : ∀ a b c w, 0 ≤ Q a b c w)
    (hQ1 : ∀ a b c, ∑ w, Q a b c w = 1) (z2 z3 z4 : β → ZMod p)
    (hz : ∀ a b c w, Q a b c w ≠ 0 →
      snorm T (z2 w) ≤ t2 ∧ snorm T (z3 w) ≤ t3 ∧ snorm T (z4 w) ≤ t4)
    (c : Fin 4 → ZMod p) (G : (Fin 4 → ZMod p) → ℝ) {B : ℝ} (hG : ∀ q, |G q| ≤ B) :
    |avg3 T r2 r3 r4 (fun x2 x3 x4 => avg3 T s2 s3 s4 (fun y2 y3 y4 =>
        ∑ w, Q x2 x3 x4 w * G (qd c (x2 + (y2 + z2 w)) (x3 + (y3 + z3 w)) (x4 + (y4 + z4 w))))) -
      qavg T r2 r3 r4 c G| ≤
      B * ((50 * T.card * t2 / s2 + 50 * T.card * t3 / s3 + 50 * T.card * t4 / s4) +
        (50 * T.card * s2 / r2 + 50 * T.card * s3 / r3 + 50 * T.card * s4 / r4)) := by
  set e1 := 50 * T.card * t2 / s2 + 50 * T.card * t3 / s3 + 50 * T.card * t4 / s4
  set e2 := 50 * T.card * s2 / r2 + 50 * T.card * s3 / r3 + 50 * T.card * s4 / r4
  set M := avg3 T r2 r3 r4 (fun x2 x3 x4 => avg3 T s2 s3 s4 (fun y2 y3 y4 =>
    G (qd c (x2 + y2) (x3 + y3) (x4 + y4))))
  -- step 1: remove the `t`-perturbation
  have S1 : |avg3 T r2 r3 r4 (fun x2 x3 x4 => avg3 T s2 s3 s4 (fun y2 y3 y4 =>
        ∑ w, Q x2 x3 x4 w * G (qd c (x2 + (y2 + z2 w)) (x3 + (y3 + z3 w)) (x4 + (y4 + z4 w))))) -
      M| ≤ B * e1 := by
    rw [avg3_sub]
    refine abs_avg3_le hr2.le hr3.le hr4.le fun a b c' _ _ _ => ?_
    rw [avg3_sum_w]
    have e : ∑ w, Q a b c' w * avg3 T s2 s3 s4 (fun y2 y3 y4 =>
        G (qd c (a + (y2 + z2 w)) (b + (y3 + z3 w)) (c' + (y4 + z4 w)))) -
        avg3 T s2 s3 s4 (fun y2 y3 y4 => G (qd c (a + y2) (b + y3) (c' + y4))) =
        ∑ w, Q a b c' w * (avg3 T s2 s3 s4 (fun y2 y3 y4 =>
        G (qd c (a + (y2 + z2 w)) (b + (y3 + z3 w)) (c' + (y4 + z4 w)))) -
        avg3 T s2 s3 s4 (fun y2 y3 y4 => G (qd c (a + y2) (b + y3) (c' + y4)))) := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hQ1, one_mul]
    rw [e]
    refine abs_wavg_le (hQ a b c') (hQ1 a b c') _ fun w hw => ?_
    obtain ⟨h2, h3, h4⟩ := hz a b c' w hw
    exact avg3_shift hs2 hs3 hs4 hst2 hst3 hst4 h2 h3 h4
      (H := fun y2 y3 y4 => G (qd c (a + y2) (b + y3) (c' + y4))) (fun _ _ _ => hG _)
  -- step 2: remove the `s`-perturbation
  have S2 : |M - qavg T r2 r3 r4 c G| ≤ B * e2 := by
    have hM : M = avg3 T s2 s3 s4 (fun y2 y3 y4 => avg3 T r2 r3 r4 (fun x2 x3 x4 =>
        G (qd c (x2 + y2) (x3 + y3) (x4 + y4)))) := avg3_comm _ _ _ _ _ _ _ _ _
    rw [hM, show qavg T r2 r3 r4 c G = avg3 T s2 s3 s4 (fun _ _ _ => qavg T r2 r3 r4 c G) from
      (avg3_const hs2.le hs3.le hs4.le _).symm, avg3_sub]
    refine abs_avg3_le hs2.le hs3.le hs4.le fun a b c' ha hb hc => ?_
    exact avg3_shift hr2 hr3 hr4 hrs2 hrs3 hrs4 (snorm_le_of_regP_ne hs2.le ha)
      (snorm_le_of_regP_ne hs3.le hb) (snorm_le_of_regP_ne hs4.le hc)
      (H := fun x2 x3 x4 => G (qd c x2 x3 x4)) (fun _ _ _ => hG _)
  have := abs_sub_le (avg3 T r2 r3 r4 (fun x2 x3 x4 => avg3 T s2 s3 s4 (fun y2 y3 y4 =>
        ∑ w, Q x2 x3 x4 w * G (qd c (x2 + (y2 + z2 w)) (x3 + (y3 + z3 w)) (x4 + (y4 + z4 w))))))
    M (qavg T r2 r3 r4 c G)
  rw [mul_add]
  linarith

end

end GT
end File_GT_U3S4a

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

/-- The Fourier-type correlation produced by the local inverse `U²` theorem. -/
def u2Vr (T : Finset (ZMod p)) (ρ0 ρ1 : ℝ) (g : ZMod p → ℝ) (u ξ : ZMod p) : ℝ :=
  ∑ n0, regP T ρ0 n0 * ‖∑ n1, (regP T ρ1 n1 : ℂ) * (g (u + n0 + n1) : ℂ) * ech (-(ξ * n1))‖ ^ 2

lemma u2Vr_nonneg (T : Finset (ZMod p)) (ρ0 ρ1 : ℝ) (g : ZMod p → ℝ) (u ξ : ZMod p) :
    0 ≤ u2Vr T ρ0 ρ1 g u ξ :=
  sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _) (sq_nonneg _)

/-- Pointwise application of the local inverse `U²` theorem. -/
lemma exists_u2Vr {T : Finset (ZMod p)} {ρ0 ρ1 ε : ℝ} (hρ1 : 0 < ρ1) (h4 : 4 * ρ1 ≤ ρ0)
    (hε : 0 ≤ ε) (hsep : 7200 * T.card * ρ1 ≤ (ε / 2) ^ 2 * ρ0) (g : ZMod p → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (u : ZMod p) :
    ∃ ξ, U2f T ρ0 ρ1 g u / 2 - ε / 4 ≤ u2Vr T ρ0 ρ1 g u ξ := by
  by_cases hU : ε / 2 ≤ U2f T ρ0 ρ1 g u
  · have hsep' : 7200 * T.card * ρ1 ≤ (U2f T ρ0 ρ1 g u) ^ 2 * ρ0 := by
      refine hsep.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
      exact pow_le_pow_left₀ (by linarith) hU 2
    have hc : ∑ h0, ∑ h0', ∑ h1, ∑ h1',
        ((regP T ρ0 h0 * regP T ρ0 h0' * regP T ρ1 h1 * regP T ρ1 h1' : ℝ) : ℂ) *
        ((g (u + (h0 + h1)) : ℂ) * conj (g (u + (h0 + h1')) : ℂ) * conj (g (u + (h0' + h1)) : ℂ) *
          (g (u + (h0' + h1')) : ℂ)) = ((U2f T ρ0 ρ1 g u : ℝ) : ℂ) := by
      unfold U2f
      push_cast
      simp only [Complex.conj_ofReal, add_assoc]
    obtain ⟨ξ, hξ⟩ := loc_u2_bohr (S := T) hρ1 h4 hsep' (by linarith)
      (fun x => (g (u + x) : ℂ)) (fun x => by rw [Complex.norm_real]; exact hg _)
      (by rw [hc, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _)
    refine ⟨ξ, ?_⟩
    have : u2Vr T ρ0 ρ1 g u ξ = ∑ n0, regP T ρ0 n0 *
        ‖∑ n1, (regP T ρ1 n1 : ℂ) * (g (u + (n0 + n1)) : ℂ) * ech (-(ξ * n1))‖ ^ 2 := by
      simp only [u2Vr, add_assoc]
    rw [this]
    linarith
  · exact ⟨0, by linarith [u2Vr_nonneg T ρ0 ρ1 g u 0]⟩

/-- The local average of `g` at the tiny scale `ρ'` with frequencies `insert ξ T`. -/
def lav (T : Finset (ZMod p)) (ξ : ZMod p) (ρ' : ℝ) (g : ZMod p → ℝ) (v : ZMod p) : ℝ :=
  ∑ w, regP (insert ξ T) ρ' w * g (v + w)

lemma abs_lav_le {T : Finset (ZMod p)} {ξ : ZMod p} {ρ' : ℝ} (hρ' : 0 ≤ ρ') {g : ZMod p → ℝ}
    (hg : ∀ x, |g x| ≤ 1) (v : ZMod p) : |lav T ξ ρ' g v| ≤ 1 :=
  abs_wavg_le (regP_isDist _ hρ').1 (regP_isDist _ hρ').2 _ fun _ _ => hg _

/-- Replacing `g` by its local average at a tiny scale inside a Fourier coefficient with
frequency `ξ`. -/
lemma u2_IJ {T : Finset (ZMod p)} {ρ1 ρ' : ℝ} (hρ1 : 0 < ρ1) (hρ' : 0 < ρ') (h4' : 4 * ρ' ≤ ρ1)
    (g : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ 1) (ξ v : ZMod p) :
    ‖∑ n1, (regP T ρ1 n1 : ℂ) * (g (v + n1) : ℂ) * ech (-(ξ * n1)) -
      ∑ n1, (regP T ρ1 n1 : ℂ) * ech (-(ξ * n1)) * (lav T ξ ρ' g (v + n1) : ℂ)‖ ≤
      50 * T.card * ρ' / ρ1 + 2 * Real.pi * ρ' := by
  set T' := insert ξ T
  have hP' := regP_isDist T' hρ'.le
  have hP1 := regP_isDist T hρ1.le
  set I := ∑ n1, (regP T ρ1 n1 : ℂ) * (g (v + n1) : ℂ) * ech (-(ξ * n1))
  set K : ZMod p → ℂ := fun w => ∑ n1, (regP T ρ1 n1 : ℂ) * ech (-(ξ * n1)) *
    (g (v + n1 + w) : ℂ)
  have hJ : ∑ n1, (regP T ρ1 n1 : ℂ) * ech (-(ξ * n1)) * (lav T ξ ρ' g (v + n1) : ℂ) =
      ∑ w, (regP T' ρ' w : ℂ) * K w := by
    simp only [K, lav, mul_sum]
    push_cast
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hI : I = ∑ w, (regP T' ρ' w : ℂ) * I := by
    rw [← sum_mul, ← Complex.ofReal_sum, hP'.2, Complex.ofReal_one, one_mul]
  rw [hJ, hI, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  refine norm_wavg_le hP'.1 hP'.2 _ fun w hw => ?_
  have hwB : w ∈ bohr T' ρ' := mem_bohr_of_regP_ne_zero hρ'.le hw
  have hws : snorm T' w ≤ ρ' := snorm_le_of_mem hwB hρ'.le
  -- shift
  have e1 := regP_shift (subset_insert ξ T) hρ1 hρ'.le h4' hwB
    (fun x => (g (v + x) : ℂ) * ech (-(ξ * x))) (B := 1) (fun x => by
      rw [norm_mul, norm_ech, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hg _)
  -- phase
  have e2 : ‖∑ x, (regP T ρ1 x : ℂ) * ((g (v + (x + w)) : ℂ) * ech (-(ξ * (x + w)))) - K w‖ ≤
      2 * Real.pi * ρ' := by
    have : ∑ x, (regP T ρ1 x : ℂ) * ((g (v + (x + w)) : ℂ) * ech (-(ξ * (x + w)))) - K w =
        ∑ x, (regP T ρ1 x : ℂ) * ((g (v + x + w) : ℂ) * ech (-(ξ * x)) *
          (ech (-(ξ * w)) - 1)) := by
      simp only [K, ← sum_sub_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [show -(ξ * (x + w)) = -(ξ * x) + -(ξ * w) by ring, ech_add, add_assoc]
      ring
    rw [this]
    refine norm_wavg_le hP1.1 hP1.2 _ fun x _ => ?_
    rw [norm_mul, norm_mul, norm_ech, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖ech (-(ξ * w)) - 1‖ ≤ 2 * Real.pi * ρ' := by
      refine (norm_ech_sub_one_le _).trans ?_
      rw [cn_neg]
      exact mul_le_mul_of_nonneg_left ((cn_le_snorm (mem_insert_self ξ T) w).trans hws)
        (by positivity)
    calc |g (v + x + w)| * ‖ech (-(ξ * w)) - 1‖ ≤ 1 * (2 * Real.pi * ρ') :=
          mul_le_mul (hg _) h1 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hIe : I = ∑ x, (regP T ρ1 x : ℂ) * ((g (v + x) : ℂ) * ech (-(ξ * x))) :=
    sum_congr rfl fun _ _ => by ring
  beta_reduce at e1
  rw [one_mul, norm_sub_rev, ← hIe] at e1
  calc ‖I - K w‖ ≤ ‖I - ∑ x, (regP T ρ1 x : ℂ) * ((g (v + (x + w)) : ℂ) *
        ech (-(ξ * (x + w))))‖ + ‖∑ x, (regP T ρ1 x : ℂ) * ((g (v + (x + w)) : ℂ) *
        ech (-(ξ * (x + w)))) - K w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add e1 e2

lemma sq_le_sq_add_of_norm {I J : ℂ} {e : ℝ} (hI : ‖I‖ ≤ 1) (hJ : ‖J‖ ≤ 1)
    (h : ‖I - J‖ ≤ e) : ‖I‖ ^ 2 ≤ ‖J‖ ^ 2 + 2 * e := by
  have h1 : ‖I‖ - ‖J‖ ≤ e := (norm_sub_norm_le I J).trans h
  have he : 0 ≤ e := (norm_nonneg _).trans h
  nlinarith [norm_nonneg I, norm_nonneg J]

/-- The Fourier correlation is controlled by the local averages at the tiny scale. -/
lemma u2Vr_le {T : Finset (ZMod p)} {ρ0 ρ1 ρ' : ℝ} (hρ1 : 0 < ρ1) (hρ' : 0 < ρ')
    (h4 : 4 * ρ1 ≤ ρ0) (h4' : 4 * ρ' ≤ ρ1) (g : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (u ξ : ZMod p) :
    u2Vr T ρ0 ρ1 g u ξ ≤ ∑ m, regP T ρ0 m * |lav T ξ ρ' g (u + m)| +
      (2 * (50 * T.card * ρ' / ρ1 + 2 * Real.pi * ρ') + 50 * T.card * ρ1 / ρ0) := by
  have hρ0 : 0 < ρ0 := by linarith
  have hP0 := regP_isDist T hρ0.le
  have hP1 := regP_isDist T hρ1.le
  set e1 := 50 * T.card * ρ' / ρ1 + 2 * Real.pi * ρ'
  set e2 := 50 * T.card * ρ1 / ρ0
  -- pointwise in `n0`
  have pt : ∀ n0, ‖∑ n1, (regP T ρ1 n1 : ℂ) * (g (u + n0 + n1) : ℂ) * ech (-(ξ * n1))‖ ^ 2 ≤
      ∑ n1, regP T ρ1 n1 * |lav T ξ ρ' g (u + n0 + n1)| + 2 * e1 := by
    intro n0
    have hIJ := u2_IJ hρ1 hρ' h4' g hg ξ (u + n0) (T := T)
    set J := ∑ n1, (regP T ρ1 n1 : ℂ) * ech (-(ξ * n1)) * (lav T ξ ρ' g (u + n0 + n1) : ℂ)
    have hJ1 : ‖J‖ ≤ ∑ n1, regP T ρ1 n1 * |lav T ξ ρ' g (u + n0 + n1)| := by
      refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n1 _ => ?_))
      rw [norm_mul, norm_mul, norm_ech, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (regP_nonneg _ _)]
    have hJle : ‖J‖ ≤ 1 := hJ1.trans (wavg_le hP1.1 hP1.2 _ fun _ _ =>
      abs_lav_le hρ'.le hg _)
    have hIle : ‖∑ n1, (regP T ρ1 n1 : ℂ) * (g (u + n0 + n1) : ℂ) * ech (-(ξ * n1))‖ ≤ 1 := by
      have e : ∑ n1, (regP T ρ1 n1 : ℂ) * (g (u + n0 + n1) : ℂ) * ech (-(ξ * n1)) =
          ∑ n1, (regP T ρ1 n1 : ℂ) * ((g (u + n0 + n1) : ℂ) * ech (-(ξ * n1))) :=
        sum_congr rfl fun _ _ => by ring
      rw [e]
      refine norm_wavg_le hP1.1 hP1.2 _ fun _ _ => ?_
      rw [norm_mul, norm_ech, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hg _
    have := sq_le_sq_add_of_norm hIle hJle hIJ
    have hJsq : ‖J‖ ^ 2 ≤ ‖J‖ := by nlinarith [norm_nonneg J]
    linarith
  -- average over `n0`
  have step1 : u2Vr T ρ0 ρ1 g u ξ ≤ ∑ n0, regP T ρ0 n0 *
      (∑ n1, regP T ρ1 n1 * |lav T ξ ρ' g (u + n0 + n1)| + 2 * e1) :=
    sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left (pt n0) (regP_nonneg _ _)
  have e2' : ∑ n0, regP T ρ0 n0 * (∑ n1, regP T ρ1 n1 * |lav T ξ ρ' g (u + n0 + n1)| + 2 * e1) =
      ∑ n1, regP T ρ1 n1 * ∑ n0, regP T ρ0 n0 * |lav T ξ ρ' g (u + (n0 + n1))| + 2 * e1 := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hP0.2, one_mul, mul_sum]
    rw [sum_comm]
    exact congrArg (· + 2 * e1) (sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by
      rw [add_assoc]; ring)
  have step2 : ∑ n1, regP T ρ1 n1 * ∑ n0, regP T ρ0 n0 * |lav T ξ ρ' g (u + (n0 + n1))| ≤
      ∑ m, regP T ρ0 m * |lav T ξ ρ' g (u + m)| + e2 := by
    have : ∑ n1, regP T ρ1 n1 * ∑ n0, regP T ρ0 n0 * |lav T ξ ρ' g (u + (n0 + n1))| -
        ∑ m, regP T ρ0 m * |lav T ξ ρ' g (u + m)| ≤ e2 := by
      rw [show ∑ m, regP T ρ0 m * |lav T ξ ρ' g (u + m)| = ∑ n1, regP T ρ1 n1 *
          ∑ m, regP T ρ0 m * |lav T ξ ρ' g (u + m)| by rw [← sum_mul, hP1.2, one_mul],
        ← sum_sub_distrib]
      simp_rw [← mul_sub]
      refine (le_abs_self _).trans (abs_wavg_le hP1.1 hP1.2 _ fun n1 hn1 => ?_)
      have := shift_real subset_rfl hρ0 h4 (snorm_le_of_regP_ne hρ1.le hn1)
        (fun x => |lav T ξ ρ' g (u + x)|) (B := 1) (fun x => by
          rw [abs_abs]; exact abs_lav_le hρ'.le hg _)
      rw [one_mul] at this
      exact this
    linarith
  linarith

lemma sq_avg3_le {T : Finset (ZMod p)} {s2 s3 s4 : ℝ} (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4)
    (H : ZMod p → ZMod p → ZMod p → ℝ) :
    (avg3 T s2 s3 s4 H) ^ 2 ≤ avg3 T s2 s3 s4 (fun a b c => (H a b c) ^ 2) := by
  rw [avg3_eq_prod, avg3_eq_prod]
  refine sq_wavg_le _ (fun v => mul_nonneg (mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _))
    (regP_nonneg _ _)) ?_
  have := avg3_const hs2 hs3 hs4 (T := T) 1
  rw [avg3_eq_prod] at this
  simpa using this

lemma sum_regP_center_shift (T : Finset (ZMod p)) (ρ : ℝ) (a : ZMod p) (F : ZMod p → ℝ) :
    ∑ u, regP T ρ (u - a) * F u = ∑ v, regP T ρ v * F (a + v) :=
  (Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun v => by simp)).symm

/-- **The estimate (bb).**  If the local `U²` norm of `g` around a random point of a Bohr
neighbourhood is large, then after adding a suitable frequency `ξ` (depending only on the
component `a + qd 0 x i`) the local averages of `g` at the tiny scale `ρ'` have large
mean square. -/
theorem u3_bb {T : Finset (ZMod p)} {r2 r3 r4 s2 s3 s4 ρ0 ρ1 ρ' ε : ℝ} (hr2 : 0 < r2)
    (hr3 : 0 < r3) (hr4 : 0 < r4) (hs2 : 0 < s2) (hs3 : 0 < s3) (hs4 : 0 < s4) (hρ1 : 0 < ρ1)
    (hρ' : 0 < ρ') (h4 : 4 * ρ1 ≤ ρ0) (h4' : 4 * ρ' ≤ ρ1) (hr : 4 * (r2 + r3) ≤ r4)
    (hs : 4 * (s2 + s3) ≤ s4) (i : Fin 4) (hq : qsc s2 s3 s4 i = ρ0) (hε : 0 ≤ ε)
    (hsep : 7200 * T.card * ρ1 ≤ (ε / 2) ^ 2 * ρ0) (g : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (a : ZMod p) (hU : ε < ∑ u, regP T (qsc r2 r3 r4 i) (u - a) * U2f T ρ0 ρ1 g u)
    (hδ : 0 ≤ ε / 4 - (2 * (50 * T.card * ρ' / ρ1 + 2 * Real.pi * ρ') + 50 * T.card * ρ1 / ρ0 +
      50 * T.card * (s2 + s3) / s4 + 50 * T.card * (r2 + r3) / r4)) :
    ∃ ξ : ZMod p → ZMod p, (ε / 4 - (2 * (50 * T.card * ρ' / ρ1 + 2 * Real.pi * ρ') +
      50 * T.card * ρ1 / ρ0 + 50 * T.card * (s2 + s3) / s4 + 50 * T.card * (r2 + r3) / r4)) ^ 2 ≤
      avg3 T r2 r3 r4 (fun x2 x3 x4 => avg3 T s2 s3 s4 (fun y2 y3 y4 =>
        (lav T (ξ (a + qd 0 x2 x3 x4 i)) ρ' g (a + qd 0 x2 x3 x4 i + qd 0 y2 y3 y4 i)) ^ 2)) := by
  have hρ0 : 0 < ρ0 := by linarith
  set e12 := 2 * (50 * T.card * ρ' / ρ1 + 2 * Real.pi * ρ') + 50 * T.card * ρ1 / ρ0
  set e3 := 50 * T.card * (s2 + s3) / s4
  set e4 := 50 * T.card * (r2 + r3) / r4
  choose ξ hξ using exists_u2Vr hρ1 h4 hε hsep g hg
  refine ⟨ξ, ?_⟩
  set q := qsc r2 r3 r4 i
  have hq0 : 0 ≤ q := by
    simp only [q, qsc]; fin_cases i <;> simp <;> linarith
  have hPq := regP_isDist T hq0
  have hPa0 : ∀ u, 0 ≤ regP T q (u - a) := fun u => regP_nonneg _ _
  have hPa1 : ∑ u, regP T q (u - a) = 1 := by
    have := sum_regP_center_shift T q a (fun _ => 1); simp only [mul_one] at this
    rw [this, hPq.2]
  set Ψ : ZMod p → ℝ := fun u => avg3 T s2 s3 s4 (fun y2 y3 y4 =>
    |lav T (ξ u) ρ' g (u + qd 0 y2 y3 y4 i)|)
  have hΨ : ∀ u, |Ψ u| ≤ 1 := fun u =>
    abs_avg3_le hs2.le hs3.le hs4.le fun _ _ _ _ _ _ => by
      rw [abs_abs]; exact abs_lav_le hρ'.le hg _
  -- A
  have A : ε / 4 ≤ ∑ u, regP T q (u - a) * u2Vr T ρ0 ρ1 g u (ξ u) := by
    have : ∑ u, regP T q (u - a) * (U2f T ρ0 ρ1 g u / 2 - ε / 4) ≤
        ∑ u, regP T q (u - a) * u2Vr T ρ0 ρ1 g u (ξ u) :=
      sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hξ u) (hPa0 u)
    have e : ∑ u, regP T q (u - a) * (U2f T ρ0 ρ1 g u / 2 - ε / 4) =
        (∑ u, regP T q (u - a) * U2f T ρ0 ρ1 g u) / 2 - ε / 4 := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hPa1, sum_div]
      congr 1
      · exact sum_congr rfl fun _ _ => by ring
      · ring
    linarith
  -- B
  have B : ∀ u, u2Vr T ρ0 ρ1 g u (ξ u) ≤ Ψ u + (e12 + e3) := by
    intro u
    have h1 := u2Vr_le hρ1 hρ' h4 h4' g hg u (ξ u) (T := T)
    have h2 := avg3_marg hs2 hs3 hs4 hs (T := T) (fun m => |lav T (ξ u) ρ' g (u + m)|) (B := 1)
      (fun x => by rw [abs_abs]; exact abs_lav_le hρ'.le hg _) i
    rw [hq, one_mul] at h2
    have h3 := (abs_le.1 h2).1
    have : Ψ u = avg3 T s2 s3 s4 (fun y2 y3 y4 => |lav T (ξ u) ρ' g (u + qd 0 y2 y3 y4 i)|) := rfl
    linarith
  -- C
  have C : ∑ u, regP T q (u - a) * Ψ u ≤
      avg3 T r2 r3 r4 (fun x2 x3 x4 => Ψ (a + qd 0 x2 x3 x4 i)) + e4 := by
    rw [sum_regP_center_shift]
    have h2 := avg3_marg hr2 hr3 hr4 hr (T := T) (fun v => Ψ (a + v)) (B := 1)
      (fun v => hΨ _) i
    rw [one_mul] at h2
    linarith [(abs_le.1 h2).1]
  have AB : ε / 4 ≤ ∑ u, regP T q (u - a) * Ψ u + (e12 + e3) := by
    have : ∑ u, regP T q (u - a) * u2Vr T ρ0 ρ1 g u (ξ u) ≤
        ∑ u, regP T q (u - a) * (Ψ u + (e12 + e3)) :=
      sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (B u) (hPa0 u)
    rw [show ∑ u, regP T q (u - a) * (Ψ u + (e12 + e3)) =
      ∑ u, regP T q (u - a) * Ψ u + (e12 + e3) by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hPa1, one_mul]] at this
    linarith
  -- D: Cauchy--Schwarz
  set X := avg3 T r2 r3 r4 (fun x2 x3 x4 => Ψ (a + qd 0 x2 x3 x4 i))
  have hX : ε / 4 - (e12 + e3 + e4) ≤ X := by linarith
  have hX2 : (ε / 4 - (e12 + e3 + e4)) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hδ hX 2
  have CS1 := sq_avg3_le hr2.le hr3.le hr4.le (T := T) (fun x2 x3 x4 => Ψ (a + qd 0 x2 x3 x4 i))
  have CS2 : avg3 T r2 r3 r4 (fun x2 x3 x4 => (Ψ (a + qd 0 x2 x3 x4 i)) ^ 2) ≤
      avg3 T r2 r3 r4 (fun x2 x3 x4 => avg3 T s2 s3 s4 (fun y2 y3 y4 =>
        (lav T (ξ (a + qd 0 x2 x3 x4 i)) ρ' g (a + qd 0 x2 x3 x4 i + qd 0 y2 y3 y4 i)) ^ 2)) := by
    refine avg3_mono hr2.le hr3.le hr4.le fun x2 x3 x4 => ?_
    have := sq_avg3_le hs2.le hs3.le hs4.le (T := T) (fun y2 y3 y4 =>
      |lav T (ξ (a + qd 0 x2 x3 x4 i)) ρ' g (a + qd 0 x2 x3 x4 i + qd 0 y2 y3 y4 i)|)
    simpa only [sq_abs] using this
  linarith

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

lemma R_anti {m n : ℕ} (h : m ≤ n) : R n ≤ R m := by
  rcases h.lt_or_eq with h' | rfl
  · exact (R_lt_le hR0 hRθ hθ0 hθ1 h').trans (by nlinarith [hR0 m])
  · exact le_rfl

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

lemma qsc_R (R : ℕ → ℝ) (j : ℕ) (i : Fin 4) : qsc (R (j + 2)) (R (j + 1)) (R j) i = R (j + lvl i) := by
  fin_cases i <;> rfl

/-- The scales of the refining quadruple for component `i`. -/
def ysc (R : ℕ → ℝ) (j : ℕ) (i : Fin 4) : ℝ × ℝ × ℝ :=
  (R (j + (12 - lvl i)), R (j + (11 - lvl i)), R (j + (10 - lvl i)))

lemma qsc_ysc (R : ℕ → ℝ) (j : ℕ) (i : Fin 4) :
    qsc (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2 i = R (j + 10) := by
  fin_cases i <;> rfl

lemma ind_nonneg (A : Finset (ZMod p)) (u : ZMod p) : 0 ≤ ind A u := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (A : Finset (ZMod p)) (u : ZMod p) : ind A u ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- The energy (variance) `E_i`. -/
def En (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) (i : Fin 4) : ℝ :=
  ∑ u, regP T (R (j + lvl i)) (u - cent c i) * (bal R A T c j i u) ^ 2

/-- The score of a neighbourhood `N = (c, j, T)`. -/
def score (R : ℕ → ℝ) (W : (Fin 4 → ZMod p) → ℝ) (A : Fin 4 → Finset (ZMod p)) (lam mu : ℝ)
    (N : (Fin 4 → ZMod p) × ℕ × Finset (ZMod p)) : ℝ :=
  QW R W N.2.2 N.1 N.2.1 - lam * ∑ i, En R A N.2.2 N.1 N.2.1 i - mu * N.2.1

/-- A shifted centre. -/
def cshift (c : Fin 4 → ZMod p) (a2 a3 a4 : ZMod p) : Fin 4 → ZMod p :=
  ![0, c 1 + a2, c 2 + a3, c 3 + a4]

lemma qd_cshift (c : Fin 4 → ZMod p) (a2 a3 a4 z2 z3 z4 : ZMod p) :
    qd (cshift c a2 a3 a4) z2 z3 z4 = qd c (a2 + z2) (a3 + z3) (a4 + z4) := by
  funext i
  fin_cases i <;> simp [qd, cshift] <;> ring

lemma cent_cshift (c : Fin 4 → ZMod p) (a2 a3 a4 : ZMod p) (i : Fin 4) :
    cent (cshift c a2 a3 a4) i = cent c i + qd 0 a2 a3 a4 i := by
  rw [cent, qd_cshift, qd_eq_cent_add]
  simp

lemma qd_zero_add (x2 x3 x4 y2 y3 y4 : ZMod p) (i : Fin 4) :
    qd 0 (x2 + y2) (x3 + y3) (x4 + y4) i = qd 0 x2 x3 x4 i + qd 0 y2 y3 y4 i := by
  fin_cases i <;> simp [qd] <;> ring

/-! ### Stability of `QW` under the random refinement -/

lemma sum3_regP_prod (T : Finset (ZMod p)) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∑ w : ZMod p × ZMod p × ZMod p, regP T a w.1 * regP T b w.2.1 * regP T c w.2.2 = 1 := by
  have := avg3_const ha hb hc (T := T) 1
  rw [avg3_eq_prod] at this
  simpa using this

lemma QW_eq_sum (W : (Fin 4 → ZMod p) → ℝ) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (a b d : ℝ) (x2 x3 x4 y2 y3 y4 : ZMod p) :
    qavg T a b d (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) W =
      ∑ w : ZMod p × ZMod p × ZMod p, (regP T a w.1 * regP T b w.2.1 * regP T d w.2.2) *
        W (qd c (x2 + (y2 + w.1)) (x3 + (y3 + w.2.1)) (x4 + (y4 + w.2.2))) := by
  unfold qavg
  simp only [Fintype.sum_prod_type, qd_cshift, add_assoc]

section stab

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16)
include hR0 hRk hθ0 hθ1

/-- The sum of the six translation errors in `absorb`, for the refinement of component `i`. -/
lemma absorb_err_le (T : Finset (ZMod p)) (j : ℕ) (i : Fin 4) :
    (50 * T.card * R (j + 20) / (ysc R j i).1 + 50 * T.card * R (j + 20) / (ysc R j i).2.1 +
      50 * T.card * R (j + 20) / (ysc R j i).2.2) +
    (50 * T.card * (ysc R j i).1 / R (j + 2) + 50 * T.card * (ysc R j i).2.1 / R (j + 1) +
      50 * T.card * (ysc R j i).2.2 / R j) ≤ 300 * T.card * θ := by
  have hθ1' : θ ≤ 1 := by linarith
  have hl := lvl_le i
  have hK : (0 : ℝ) ≤ 50 * T.card := by positivity
  simp only [ysc]
  have := ratio_le_sc hR0 hRk hθ0 hθ1' _ hK (m := j + (12 - lvl i)) (n := j + 20) (by omega)
  have := ratio_le_sc hR0 hRk hθ0 hθ1' _ hK (m := j + (11 - lvl i)) (n := j + 20) (by omega)
  have := ratio_le_sc hR0 hRk hθ0 hθ1' _ hK (m := j + (10 - lvl i)) (n := j + 20) (by omega)
  have := ratio_le_sc hR0 hRk hθ0 hθ1' _ hK (m := j + 2) (n := j + (12 - lvl i)) (by omega)
  have := ratio_le_sc hR0 hRk hθ0 hθ1' _ hK (m := j + 1) (n := j + (11 - lvl i)) (by omega)
  have := ratio_le_sc hR0 hRk hθ0 hθ1' _ hK (m := j) (n := j + (10 - lvl i)) (by omega)
  linarith

/-- **(letitgo)**: the weighted average is stable under the random refinement. -/
theorem QW_refine (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4)
    (Ξ : ZMod p → ZMod p → ZMod p → ZMod p) (W : (Fin 4 → ZMod p) → ℝ) {B : ℝ}
    (hW : ∀ q, |W q| ≤ B) :
    |avg3 T (R (j + 2)) (R (j + 1)) (R j) (fun x2 x3 x4 =>
        avg3 T (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2 (fun y2 y3 y4 =>
          QW R W (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20))) -
      QW R W T c j| ≤ B * (300 * T.card * θ) := by
  have hθ1' : θ ≤ 1 := by linarith
  have hl := lvl_le i
  have hB : 0 ≤ B := (abs_nonneg _).trans (hW 0)
  have f4 : ∀ m n, m < n → 4 * R n ≤ R m := fun m n h => four_R_le hR0 hRk hθ0 hθ1' h hθ1
  have ab := absorb (T := T) (hR0 (j + 2)) (hR0 (j + 1)) (hR0 j) (hR0 _) (hR0 _) (hR0 _)
    (f4 _ _ (by omega)) (f4 _ _ (by omega)) (f4 _ _ (by omega))
    (f4 (j + (12 - lvl i)) (j + 20) (by omega)) (f4 (j + (11 - lvl i)) (j + 20) (by omega))
    (f4 (j + (10 - lvl i)) (j + 20) (by omega))
    (fun x2 x3 x4 (w : ZMod p × ZMod p × ZMod p) => regP (insert (Ξ x2 x3 x4) T) (R (j + 20 + 2)) w.1 *
      regP (insert (Ξ x2 x3 x4) T) (R (j + 20 + 1)) w.2.1 *
      regP (insert (Ξ x2 x3 x4) T) (R (j + 20)) w.2.2)
    (fun _ _ _ _ => mul_nonneg (mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)) (regP_nonneg _ _))
    (fun _ _ _ => sum3_regP_prod _ (hR0 _).le (hR0 _).le (hR0 _).le)
    (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2) ?_ c W hW
  · have e : avg3 T (R (j + 2)) (R (j + 1)) (R j) (fun x2 x3 x4 =>
        avg3 T (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2 (fun y2 y3 y4 =>
          QW R W (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20))) =
        avg3 T (R (j + 2)) (R (j + 1)) (R j) (fun x2 x3 x4 =>
        avg3 T (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2 (fun y2 y3 y4 =>
          ∑ w : ZMod p × ZMod p × ZMod p, (regP (insert (Ξ x2 x3 x4) T) (R (j + 20 + 2)) w.1 *
            regP (insert (Ξ x2 x3 x4) T) (R (j + 20 + 1)) w.2.1 *
            regP (insert (Ξ x2 x3 x4) T) (R (j + 20)) w.2.2) *
          W (qd c (x2 + (y2 + w.1)) (x3 + (y3 + w.2.1)) (x4 + (y4 + w.2.2))))) := by
      unfold QW
      simp only [QW_eq_sum]
    rw [e]
    refine ab.trans (mul_le_mul_of_nonneg_left ?_ hB)
    exact absorb_err_le hR0 hRk hθ0 hθ1 T j i
  · intro x2 x3 x4 w hw
    have h1 : regP (insert (Ξ x2 x3 x4) T) (R (j + 20 + 2)) w.1 ≠ 0 := fun h => hw (by simp [h])
    have h2 : regP (insert (Ξ x2 x3 x4) T) (R (j + 20 + 1)) w.2.1 ≠ 0 :=
      fun h => hw (by simp [h])
    have h3 : regP (insert (Ξ x2 x3 x4) T) (R (j + 20)) w.2.2 ≠ 0 := fun h => hw (by simp [h])
    refine ⟨?_, ?_, ?_⟩
    · exact (snorm_mono (subset_insert _ _) _).trans ((snorm_le_of_regP_ne (hR0 _).le h1).trans
        (R_anti hR0 hRk hθ0 hθ1' (by omega)))
    · exact (snorm_mono (subset_insert _ _) _).trans ((snorm_le_of_regP_ne (hR0 _).le h2).trans
        (R_anti hR0 hRk hθ0 hθ1' (by omega)))
    · exact (snorm_mono (subset_insert _ _) _).trans (snorm_le_of_regP_ne (hR0 _).le h3)

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

/-- Pythagoras' theorem for a variance. -/
lemma var_eq_sub {α : Type*} [Fintype α] {P : α → ℝ} (hP1 : ∑ x, P x = 1) (g : α → ℝ) (a : ℝ) :
    ∑ x, P x * (g x - ∑ y, P y * g y) ^ 2 =
      ∑ x, P x * (g x - a) ^ 2 - (∑ y, P y * g y - a) ^ 2 := by
  set m := ∑ y, P y * g y with hm
  have e : ∀ x, P x * (g x - m) ^ 2 =
      P x * (g x - a) ^ 2 - 2 * (m - a) * (P x * g x) + (2 * (m - a) * a + (m - a) ^ 2) * P x :=
    fun x => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hP1, ← hm]
  ring

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

lemma En_nonneg (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) : 0 ≤ En R A T c j i :=
  sum_nonneg fun _ _ => mul_nonneg (regP_nonneg _ _) (sq_nonneg _)

lemma En_le_one {R : ℕ → ℝ} (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) (hR : 0 ≤ R (j + lvl i)) : En R A T c j i ≤ 1 := by
  unfold En
  calc ∑ u, regP T (R (j + lvl i)) (u - cent c i) * (bal R A T c j i u) ^ 2
      ≤ ∑ u, regP T (R (j + lvl i)) (u - cent c i) * 1 := by
        refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (regP_nonneg _ _)
        have := abs_bal_le A T c j i hR u
        nlinarith [abs_nonneg (bal R A T c j i u), sq_abs (bal R A T c j i u)]
    _ = 1 := by simp only [mul_one]; exact sum_regP_center' T hR _

/-- Pythagoras for the energy: `E_i + (α_i - a)² = E|1_{A_i} - a|²`. -/
lemma En_add_sq {R : ℕ → ℝ} (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) (hR : 0 ≤ R (j + lvl i)) (a : ℝ) :
    En R A T c j i + (alph R A T c j i - a) ^ 2 =
      ∑ v, regP T (R (j + lvl i)) v * (ind (A i) (cent c i + v) - a) ^ 2 := by
  have h1 := var_eq_sub (P := fun u => regP T (R (j + lvl i)) (u - cent c i))
    (sum_regP_center' T hR _) (ind (A i)) a
  have hE : En R A T c j i = ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
      (ind (A i) u - ∑ y, regP T (R (j + lvl i)) (y - cent c i) * ind (A i) y) ^ 2 := rfl
  rw [hE, h1, sum_regP_center_shift T _ (cent c i) (fun u => (ind (A i) u - a) ^ 2)]
  simp only [alph]
  ring

/-- The displacement putting `v` into the component `i'` of a centred quadruple. -/
def zdisp (i' : Fin 4) (v : ZMod p) : ZMod p × ZMod p × ZMod p :=
  (if i' = 1 then v else 0, if i' = 2 then v else 0, if i' = 0 ∨ i' = 3 then v else 0)

lemma qd_zdisp (i' : Fin 4) (v : ZMod p) :
    qd 0 (zdisp i' v).1 (zdisp i' v).2.1 (zdisp i' v).2.2 i' = v := by
  fin_cases i' <;> simp [zdisp, qd]

lemma qd_add3 (x2 x3 x4 y2 y3 y4 z2 z3 z4 : ZMod p) (i : Fin 4) :
    qd 0 (x2 + (y2 + z2)) (x3 + (y3 + z3)) (x4 + (y4 + z4)) i =
      qd 0 x2 x3 x4 i + qd 0 y2 y3 y4 i + qd 0 z2 z3 z4 i := by
  rw [qd_zero_add, qd_zero_add]; ring

section refine

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16)
include hR0 hRk hθ0 hθ1

/-- **(estable), first part.**  Under the random refinement (driven by the component `i`), the
expected energy of any component `i'`, plus the expected squared change of its density, is at
most the old energy (up to a negligible error). -/
theorem En_refine (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ) (i i' : Fin 4)
    (Ξ : ZMod p → ZMod p → ZMod p → ZMod p) (A : Fin 4 → Finset (ZMod p)) :
    avg3 T (R (j + 2)) (R (j + 1)) (R j) (fun x2 x3 x4 =>
        avg3 T (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2 (fun y2 y3 y4 =>
          En R A (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' +
          (alph R A (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' -
            alph R A T c j i') ^ 2)) ≤ En R A T c j i' + 400 * T.card * θ := by
  have hθ1' : θ ≤ 1 := by linarith
  have hl := lvl_le i
  have hl' := lvl_le i'
  have f4 : ∀ m n, m < n → 4 * R n ≤ R m := fun m n h => four_R_le hR0 hRk hθ0 hθ1' h hθ1
  set α := alph R A T c j i' with hα
  have hα0 : 0 ≤ α := alph_nonneg R A T c j i'
  have hα1 : α ≤ 1 := alph_le_one A T c j i' (hR0 _).le
  set G : (Fin 4 → ZMod p) → ℝ := fun q => (ind (A i') (q i') - α) ^ 2 with hG
  have hGb : ∀ q, |G q| ≤ 1 := fun q => by
    have := ind_nonneg (A i') (q i')
    have := ind_le_one (A i') (q i')
    rw [hG, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  -- step a: pointwise identity
  have hpt : ∀ x2 x3 x4 y2 y3 y4,
      En R A (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' +
        (alph R A (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' -
          α) ^ 2 =
      ∑ v, regP (insert (Ξ x2 x3 x4) T) (R (j + 20 + lvl i')) v *
        G (qd c (x2 + (y2 + (zdisp i' v).1)) (x3 + (y3 + (zdisp i' v).2.1))
          (x4 + (y4 + (zdisp i' v).2.2))) := by
    intro x2 x3 x4 y2 y3 y4
    rw [En_add_sq A _ _ (j + 20) i' (hR0 _).le α]
    refine sum_congr rfl fun v _ => ?_
    congr 3
    rw [qd_eq_cent_add c _ _ _ i', qd_add3, qd_zdisp, cent_cshift, qd_zero_add]
    congr 1
    ring
  simp_rw [hpt]
  -- step b: absorb
  have hab := absorb (T := T) (hR0 (j + 2)) (hR0 (j + 1)) (hR0 j) (hR0 _) (hR0 _) (hR0 _)
    (f4 _ _ (by omega)) (f4 _ _ (by omega)) (f4 _ _ (by omega))
    (f4 (j + (12 - lvl i)) (j + 20) (by omega)) (f4 (j + (11 - lvl i)) (j + 20) (by omega))
    (f4 (j + (10 - lvl i)) (j + 20) (by omega))
    (fun x2 x3 x4 v => regP (insert (Ξ x2 x3 x4) T) (R (j + 20 + lvl i')) v)
    (fun _ _ _ _ => regP_nonneg _ _) (fun _ _ _ => sum_regP _ (hR0 _).le)
    (fun v => (zdisp i' v).1) (fun v => (zdisp i' v).2.1) (fun v => (zdisp i' v).2.2) ?_ c G hGb
  swap
  · intro x2 x3 x4 v hv
    have hs : snorm T v ≤ R (j + 20) :=
      (snorm_mono (subset_insert _ _) _).trans ((snorm_le_of_regP_ne (hR0 _).le hv).trans
        (R_anti hR0 hRk hθ0 hθ1' (by omega)))
    have h0 : snorm T (0 : ZMod p) ≤ R (j + 20) := by rw [snorm_zero]; exact (hR0 _).le
    refine ⟨?_, ?_, ?_⟩ <;> simp only [zdisp] <;> split_ifs <;> assumption
  have herr := absorb_err_le hR0 hRk hθ0 hθ1 T j i
  rw [one_mul] at hab
  -- step c: marginal
  have hmarg := avg3_marg (hR0 (j + 2)) (hR0 (j + 1)) (hR0 j)
    (four_R2_le hR0 hRk hθ0 hθ1' (by omega) (by omega) hθ1) (T := T)
    (fun u => (ind (A i') (cent c i' + u) - α) ^ 2) (B := 1) (fun u => hGb (fun _ => cent c i' + u))
    i'
  rw [one_mul, qsc_R] at hmarg
  have hq : qavg T (R (j + 2)) (R (j + 1)) (R j) c G = avg3 T (R (j + 2)) (R (j + 1)) (R j)
      (fun x2 x3 x4 => (ind (A i') (cent c i' + qd 0 x2 x3 x4 i') - α) ^ 2) := by
    rw [qavg_eq_avg3]
    congr 1
    funext x2 x3 x4
    simp only [hG]
    rw [qd_eq_cent_add c _ _ _ i']
  have hE : ∑ u, regP T (R (j + lvl i')) u * (ind (A i') (cent c i' + u) - α) ^ 2 =
      En R A T c j i' := by
    have := En_add_sq A T c j i' (hR0 _).le α
    rw [← hα, sub_self] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at this
    exact this.symm
  rw [hq] at hab
  rw [hE] at hmarg
  have hr : 50 * T.card * (R (j + 2) + R (j + 1)) / R j ≤ 100 * T.card * θ := by
    have h1 := hRk j
    have h2 := hRk (j + 1)
    have h3 : R (j + 2) ≤ θ * R j := h2.trans (by nlinarith [hR0 j, hR0 (j + 1)])
    rw [div_le_iff₀ (hR0 j)]
    have hT : (0 : ℝ) ≤ T.card := by positivity
    nlinarith
  beta_reduce at hab
  simp only [ysc] at herr hab ⊢
  have := (abs_le.1 hab).2
  have := (abs_le.1 hmarg).2
  linarith

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

/-- The double average over a random quadruple and a refining random quadruple. -/
def avg33 (T : Finset (ZMod p)) (r2 r3 r4 s2 s3 s4 : ℝ)
    (F : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ) : ℝ :=
  avg3 T r2 r3 r4 (fun x2 x3 x4 => avg3 T s2 s3 s4 (fun y2 y3 y4 => F x2 x3 x4 y2 y3 y4))

section avg33

variable (T : Finset (ZMod p)) (r2 r3 r4 s2 s3 s4 : ℝ)

lemma avg33_add (F G : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ) :
    avg33 T r2 r3 r4 s2 s3 s4 (fun a b c d e f => F a b c d e f + G a b c d e f) =
      avg33 T r2 r3 r4 s2 s3 s4 F + avg33 T r2 r3 r4 s2 s3 s4 G := by
  unfold avg33; simp only [avg3_add]

lemma avg33_sub (F G : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ) :
    avg33 T r2 r3 r4 s2 s3 s4 (fun a b c d e f => F a b c d e f - G a b c d e f) =
      avg33 T r2 r3 r4 s2 s3 s4 F - avg33 T r2 r3 r4 s2 s3 s4 G := by
  unfold avg33; simp only [← avg3_sub]

lemma avg33_smul (a : ℝ) (F : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ) :
    avg33 T r2 r3 r4 s2 s3 s4 (fun x2 x3 x4 y2 y3 y4 => a * F x2 x3 x4 y2 y3 y4) =
      a * avg33 T r2 r3 r4 s2 s3 s4 F := by
  unfold avg33; simp only [avg3_smul]

variable {r2 r3 r4 s2 s3 s4} (hr2 : 0 ≤ r2) (hr3 : 0 ≤ r3) (hr4 : 0 ≤ r4) (hs2 : 0 ≤ s2)
  (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4)
include hr2 hr3 hr4 hs2 hs3 hs4

lemma avg33_const (a : ℝ) : avg33 T r2 r3 r4 s2 s3 s4 (fun _ _ _ _ _ _ => a) = a := by
  unfold avg33; simp only [avg3_const hs2 hs3 hs4, avg3_const hr2 hr3 hr4]

lemma avg33_mono {F G : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ}
    (h : ∀ a b c d e f, F a b c d e f ≤ G a b c d e f) :
    avg33 T r2 r3 r4 s2 s3 s4 F ≤ avg33 T r2 r3 r4 s2 s3 s4 G :=
  avg3_mono hr2 hr3 hr4 fun a b c => avg3_mono hs2 hs3 hs4 fun d e f => h a b c d e f

lemma avg33_le_of_le {F : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ} {B : ℝ}
    (h : ∀ a b c d e f, F a b c d e f ≤ B) : avg33 T r2 r3 r4 s2 s3 s4 F ≤ B := by
  have := avg33_mono T hr2 hr3 hr4 hs2 hs3 hs4 h (G := fun _ _ _ _ _ _ => B)
  rwa [avg33_const T hr2 hr3 hr4 hs2 hs3 hs4] at this

end avg33

/-- The change of the density of the refined component is a local average of the balanced
function at the tiny scale. -/
lemma alph_refine_eq (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) (hR : 0 ≤ R (j + 20 + lvl i)) (ξ : ZMod p)
    (x2 x3 x4 y2 y3 y4 : ZMod p) :
    alph R A (insert ξ T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i -
      alph R A T c j i = lav T ξ (R (j + 20 + lvl i)) (bal R A T c j i)
        (cent c i + qd 0 x2 x3 x4 i + qd 0 y2 y3 y4 i) := by
  have h1 := sum_regP (insert ξ T) hR
  have e : alph R A (insert ξ T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i =
      ∑ v, regP (insert ξ T) (R (j + 20 + lvl i)) v *
        ind (A i) (cent c i + qd 0 x2 x3 x4 i + qd 0 y2 y3 y4 i + v) := by
    unfold alph
    rw [sum_regP_center_shift, cent_cshift, qd_zero_add, add_assoc (cent c i)]
  rw [e]
  unfold lav bal
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, h1, one_mul]

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

/-- **The energy decrement.**  If the balanced function of the component `i` has a large local
`U²` norm, then the random refinement increases the score on average. -/
theorem score_refine (hR1 : R 0 ≤ 1) (W : (Fin 4 → ZMod p) → ℝ) {B : ℝ}
    (hW : ∀ q, |W q| ≤ B) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p))
    (c : Fin 4 → ZMod p) (j : ℕ) (i : Fin 4) {lam mu ε : ℝ} (hlam : 0 ≤ lam) (hε : 0 ≤ ε)
    (hsep : 7200 * T.card * θ ≤ (ε / 2) ^ 2) (herr : (350 * T.card + 13) * θ ≤ ε / 8)
    (hU : ε < ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
      U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u) :
    ∃ Ξ : ZMod p → ZMod p → ZMod p → ZMod p,
      score R W A lam mu (c, j, T) + lam * (ε / 8) ^ 2 - B * (300 * T.card * θ) -
        lam * (1600 * T.card * θ) - 20 * mu ≤
      avg33 T (R (j + 2)) (R (j + 1)) (R j) (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2
        (fun x2 x3 x4 y2 y3 y4 => score R W A lam mu
          (cshift c (x2 + y2) (x3 + y3) (x4 + y4), j + 20, insert (Ξ x2 x3 x4) T)) := by
  have hθ1' : θ ≤ 1 := by linarith
  have hl := lvl_le i
  have f4 : ∀ m n, m < n → 4 * R n ≤ R m := fun m n h => four_R_le hR0 hRk hθ0 hθ1' h hθ1
  have hT : (0 : ℝ) ≤ T.card := by positivity
  set ρ' := R (j + 20 + lvl i)
  set g := bal R A T c j i
  have hg : ∀ x, |g x| ≤ 1 := abs_bal_le A T c j i (hR0 _).le
  -- the error in the estimate (bb)
  set ebb := 2 * (50 * T.card * ρ' / R (j + 11) + 2 * Real.pi * ρ') +
    50 * T.card * R (j + 11) / R (j + 10) +
    50 * T.card * ((ysc R j i).1 + (ysc R j i).2.1) / (ysc R j i).2.2 +
    50 * T.card * (R (j + 2) + R (j + 1)) / R j with hebb
  have hebb_le : ebb ≤ ε / 8 := by
    have e1 : 50 * T.card * ρ' / R (j + 11) ≤ 50 * T.card * θ :=
      ratio_le_sc hR0 hRk hθ0 hθ1' _ (by positivity) (by omega)
    have e2 : ρ' ≤ θ := by
      have := R_lt_le hR0 hRk hθ0 hθ1' (show 0 < j + 20 + lvl i by omega)
      nlinarith [hR0 0]
    have e3 : 50 * T.card * R (j + 11) / R (j + 10) ≤ 50 * T.card * θ :=
      ratio_le_sc hR0 hRk hθ0 hθ1' _ (by positivity) (by omega)
    have e4 : 50 * T.card * ((ysc R j i).1 + (ysc R j i).2.1) / (ysc R j i).2.2 ≤
        50 * T.card * (2 * θ) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (ratio_sum2 hR0 hRk hθ0 hθ1 (by omega) (by omega))
        (by positivity)
    have e5 : 50 * T.card * (R (j + 2) + R (j + 1)) / R j ≤ 50 * T.card * (2 * θ) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (ratio_sum2 hR0 hRk hθ0 hθ1 (by omega) (by omega))
        (by positivity)
    have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have e6 : Real.pi * ρ' ≤ 3.15 * θ := by nlinarith [Real.pi_pos, hR0 (j + 20 + lvl i)]
    rw [hebb]
    linarith
  have hδ : 0 ≤ ε / 4 - ebb := by linarith
  have hδ8 : ε / 8 ≤ ε / 4 - ebb := by linarith
  obtain ⟨ξ, hξ⟩ := u3_bb (T := T) (hR0 (j + 2)) (hR0 (j + 1)) (hR0 j) (hR0 _) (hR0 _) (hR0 _)
    (hR0 (j + 11)) (hR0 (j + 20 + lvl i)) (f4 _ _ (by omega)) (f4 _ _ (by omega))
    (four_R2_le hR0 hRk hθ0 hθ1' (by omega) (by omega) hθ1)
    (four_R2_le hR0 hRk hθ0 hθ1' (by omega) (by omega) hθ1) i (qsc_ysc R j i) hε
    (by
      have h1 : R (j + 11) ≤ θ * R (j + 10) := hRk (j + 10)
      have := hR0 (j + 10)
      nlinarith)
    g hg (cent c i) (by rw [qsc_R]; exact hU) hδ
  set Ξ : ZMod p → ZMod p → ZMod p → ZMod p := fun x2 x3 x4 => ξ (cent c i + qd 0 x2 x3 x4 i)
  refine ⟨Ξ, ?_⟩
  -- the pointwise lower bound for the new score
  set Φ : Fin 4 → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ :=
    fun i' x2 x3 x4 y2 y3 y4 =>
      En R A (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' +
      (alph R A (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' -
        alph R A T c j i') ^ 2
  set Ψ : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ :=
    fun x2 x3 x4 y2 y3 y4 => (lav T (ξ (cent c i + qd 0 x2 x3 x4 i)) ρ' g
      (cent c i + qd 0 x2 x3 x4 i + qd 0 y2 y3 y4 i)) ^ 2
  set Q : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ :=
    fun x2 x3 x4 y2 y3 y4 =>
      QW R W (insert (Ξ x2 x3 x4) T) (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20)
  have hpt : ∀ x2 x3 x4 y2 y3 y4,
      Q x2 x3 x4 y2 y3 y4 - lam * (Φ 0 x2 x3 x4 y2 y3 y4 + Φ 1 x2 x3 x4 y2 y3 y4 +
        Φ 2 x2 x3 x4 y2 y3 y4 + Φ 3 x2 x3 x4 y2 y3 y4) + lam * Ψ x2 x3 x4 y2 y3 y4 -
        mu * ((j : ℝ) + 20) ≤
      score R W A lam mu (cshift c (x2 + y2) (x3 + y3) (x4 + y4), j + 20,
        insert (Ξ x2 x3 x4) T) := by
    intro x2 x3 x4 y2 y3 y4
    have hΨ : Ψ x2 x3 x4 y2 y3 y4 = (alph R A (insert (Ξ x2 x3 x4) T)
        (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i - alph R A T c j i) ^ 2 := by
      simp only [Ψ, Ξ]
      rw [alph_refine_eq R A T c j i (hR0 _).le]
    have hsq : ∀ i', 0 ≤ (alph R A (insert (Ξ x2 x3 x4) T)
        (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' - alph R A T c j i') ^ 2 :=
      fun _ => sq_nonneg _
    have hsum : Ψ x2 x3 x4 y2 y3 y4 ≤ ∑ i', (alph R A (insert (Ξ x2 x3 x4) T)
        (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' - alph R A T c j i') ^ 2 := by
      rw [hΨ]
      exact single_le_sum (f := fun i' => (alph R A (insert (Ξ x2 x3 x4) T)
        (cshift c (x2 + y2) (x3 + y3) (x4 + y4)) (j + 20) i' - alph R A T c j i') ^ 2)
        (fun i' _ => hsq i') (mem_univ i)
    simp only [score, Q, Φ, Fin.sum_univ_four] at hsum ⊢
    push_cast
    nlinarith
  -- averaging
  have hr2 := (hR0 (j + 2)).le
  have hr3 := (hR0 (j + 1)).le
  have hr4 := (hR0 j).le
  have hs2' : 0 ≤ (ysc R j i).1 := (hR0 _).le
  have hs3' : 0 ≤ (ysc R j i).2.1 := (hR0 _).le
  have hs4' : 0 ≤ (ysc R j i).2.2 := (hR0 _).le
  refine le_trans ?_ (avg33_mono T hr2 hr3 hr4 hs2' hs3' hs4' hpt)
  rw [avg33_sub, avg33_add, avg33_sub, avg33_smul, avg33_smul, avg33_add, avg33_add, avg33_add,
    avg33_const T hr2 hr3 hr4 hs2' hs3' hs4']
  -- the four ingredients
  have hQ := QW_refine hR0 hRk hθ0 hθ1 T c j i Ξ W hW
  have hQ' : QW R W T c j - B * (300 * T.card * θ) ≤ avg33 T (R (j + 2)) (R (j + 1)) (R j)
      (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2 Q :=
    by have := (abs_le.1 hQ).1; unfold avg33; linarith
  have hΦ : ∀ i', lam * avg33 T (R (j + 2)) (R (j + 1)) (R j)
      (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2 (Φ i') ≤
      lam * (En R A T c j i' + 400 * T.card * θ) :=
    fun i' => mul_le_mul_of_nonneg_left (En_refine hR0 hRk hθ0 hθ1 T c j i i' Ξ A) hlam
  have hΨ : lam * (ε / 8) ^ 2 ≤ lam * avg33 T (R (j + 2)) (R (j + 1)) (R j)
      (ysc R j i).1 (ysc R j i).2.1 (ysc R j i).2.2 Ψ := by
    have : (ε / 8) ^ 2 ≤ (ε / 4 - ebb) ^ 2 := pow_le_pow_left₀ (by positivity) hδ8 2
    exact mul_le_mul_of_nonneg_left (this.trans hξ) hlam
  have h0 := hΦ 0
  have h1 := hΦ 1
  have h2 := hΦ 2
  have h3 := hΦ 3
  simp only [score, Fin.sum_univ_four]
  simp only [mul_add] at h0 h1 h2 h3 ⊢
  linarith

end refine

open Classical in
/-- **Theorem 9.5** (fourth step): a neighbourhood on which the weighted average of `W` is still
large and all the sets `A_i` are locally pseudorandom. -/
theorem u3_step4 {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) (hR1 : R 0 ≤ 1) (S : Finset (ZMod p))
    (W : (Fin 4 → ZMod p) → ℝ) {B : ℝ} (hW : ∀ q, |W q| ≤ B) (hW1 : ∀ q, W q ≤ 1)
    (A : Fin 4 → Finset (ZMod p)) (c0 : Fin 4 → ZMod p) {c3 ε mu : ℝ} {K : ℕ}
    (hc3 : 0 < c3) (hε : 0 < ε) (hmu : 0 < mu) (hQ0 : c3 ≤ QW R W S c0 0)
    (hmuε : 20 * mu ≤ c3 / 8 * (ε / 8) ^ 2 / 4) (hK : 1 + 20 * mu ≤ 20 * mu * K)
    (hθK : (B * 300 + c3 / 8 * 1600) * (S.card + K) * θ ≤ c3 / 8 * (ε / 8) ^ 2 / 4)
    (hsep : 7200 * (S.card + K) * θ ≤ (ε / 2) ^ 2)
    (herr : (350 * (S.card + K) + 13) * θ ≤ ε / 8) :
    ∃ (c : Fin 4 → ZMod p) (k : ℕ) (T : Finset (ZMod p)), S ⊆ T ∧ T.card ≤ S.card + k ∧
      k < K ∧ c3 / 2 ≤ QW R W T c (20 * k) ∧
      ∀ i, ∑ u, regP T (R (20 * k + lvl i)) (u - cent c i) *
        U2f T (R (20 * k + 10)) (R (20 * k + 11)) (bal R A T c (20 * k) i) u ≤ ε := by
  set lam := c3 / 8 with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set NS := ((univ : Finset (Fin 4 → ZMod p)) ×ˢ (range K) ×ˢ
    (univ : Finset (Finset (ZMod p)))).filter
    (fun N => S ⊆ N.2.2 ∧ N.2.2.card ≤ S.card + N.2.1) with hNS
  set sc : (Fin 4 → ZMod p) × ℕ × Finset (ZMod p) → ℝ :=
    fun N => score R W A lam mu (N.1, 20 * N.2.1, N.2.2) with hsc
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hK; simp at hK; linarith
    · exact h
  have hN0 : ((c0, 0, S) : (Fin 4 → ZMod p) × ℕ × Finset (ZMod p)) ∈ NS := by
    simp [hNS, hK0]
  obtain ⟨N, hN, hmax⟩ := exists_max_image NS sc ⟨_, hN0⟩
  obtain ⟨c, k, T⟩ := N
  have hN' := hN
  simp only [hNS, mem_filter, mem_product, mem_univ, mem_range, true_and, and_true] at hN'
  obtain ⟨hkK, hST, hTc⟩ := hN'
  have hB : 0 ≤ B := (abs_nonneg _).trans (hW 0)
  have hEn : ∀ (T' : Finset (ZMod p)) (c' : Fin 4 → ZMod p) (j : ℕ) i,
      En R A T' c' j i ≤ 1 := fun T' c' j i => En_le_one A T' c' j i (hR0 _).le
  have hEn0 : ∀ (T' : Finset (ZMod p)) (c' : Fin 4 → ZMod p) (j : ℕ) i,
      0 ≤ En R A T' c' j i := fun T' c' j i => En_nonneg R A T' c' j i
  have hsc0 : c3 / 2 ≤ sc (c0, 0, S) := by
    simp only [hsc, score, Fin.sum_univ_four, mul_zero, Nat.cast_zero]
    have := hEn S c0 0 0
    have := hEn S c0 0 1
    have := hEn S c0 0 2
    have := hEn S c0 0 3
    nlinarith
  have hscN := hmax _ hN0
  have hQW1 : QW R W T c (20 * k) ≤ 1 := qavg_le_one (hR0 _).le (hR0 _).le (hR0 _).le c hW1
  have hscN' : sc (c, k, T) = QW R W T c (20 * k) -
      lam * (En R A T c (20 * k) 0 + En R A T c (20 * k) 1 + En R A T c (20 * k) 2 +
        En R A T c (20 * k) 3) - mu * (20 * k) := by
    simp only [hsc, score, Fin.sum_univ_four]; push_cast; ring
  have hsumE : 0 ≤ lam * (En R A T c (20 * k) 0 + En R A T c (20 * k) 1 + En R A T c (20 * k) 2 +
        En R A T c (20 * k) 3) := by
    have := hEn0 T c (20 * k) 0
    have := hEn0 T c (20 * k) 1
    have := hEn0 T c (20 * k) 2
    have := hEn0 T c (20 * k) 3
    exact mul_nonneg hlam0 (by linarith)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmuk : 0 ≤ mu * (20 * k) := mul_nonneg hmu.le (by linarith)
  have hQ : c3 / 2 ≤ QW R W T c (20 * k) := by linarith
  have hkmu : mu * (20 * k) ≤ 1 - c3 / 2 := by linarith
  refine ⟨c, k, T, hST, hTc, hkK, hQ, fun i => ?_⟩
  by_contra hbad
  push_neg at hbad
  have hTK : (T.card : ℝ) ≤ S.card + K := by
    have : (T.card : ℝ) ≤ S.card + k := by exact_mod_cast hTc
    have : (k : ℝ) ≤ K := by exact_mod_cast hkK.le
    linarith
  have hsep' : 7200 * T.card * θ ≤ (ε / 2) ^ 2 :=
    le_trans (by gcongr) hsep
  have herr' : (350 * T.card + 13) * θ ≤ ε / 8 :=
    le_trans (by gcongr) herr
  obtain ⟨Ξ, hΞ⟩ := score_refine hR0 hRk hθ0 hθ1 hR1 W hW A T c (20 * k) i (lam := lam)
    (mu := mu) hlam0 hε.le hsep' herr' hbad
  have hk1 : k + 1 < K := by
    have h1 : mu * (20 * (k + 1 : ℕ)) < 20 * mu * K := by push_cast; nlinarith
    have : ((k + 1 : ℕ) : ℝ) < K := by nlinarith
    exact_mod_cast this
  have hle : ∀ x2 x3 x4 y2 y3 y4 : ZMod p, score R W A lam mu
      (cshift c (x2 + y2) (x3 + y3) (x4 + y4), 20 * k + 20, insert (Ξ x2 x3 x4) T) ≤
      sc (c, k, T) := by
    intro x2 x3 x4 y2 y3 y4
    have hmem : ((cshift c (x2 + y2) (x3 + y3) (x4 + y4), k + 1, insert (Ξ x2 x3 x4) T) :
        (Fin 4 → ZMod p) × ℕ × Finset (ZMod p)) ∈ NS := by
      simp only [hNS, mem_filter, mem_product, mem_univ, mem_range, true_and, and_true]
      refine ⟨hk1, hST.trans (subset_insert _ _), ?_⟩
      have := card_insert_le (Ξ x2 x3 x4) T
      omega
    have := hmax _ hmem
    simpa only [hsc, mul_add, mul_one] using this
  have hav := avg33_le_of_le T (hR0 _).le (hR0 _).le (hR0 _).le (hR0 _).le (hR0 _).le (hR0 _).le
    (r2 := R (20 * k + 2)) (r3 := R (20 * k + 1)) (r4 := R (20 * k))
    (s2 := (ysc R (20 * k) i).1) (s3 := (ysc R (20 * k) i).2.1) (s4 := (ysc R (20 * k) i).2.2) hle
  have hscore : sc (c, k, T) = score R W A lam mu (c, 20 * k, T) := rfl
  rw [← hscore] at hΞ
  have hg1 : B * (300 * T.card * θ) + lam * (1600 * T.card * θ) ≤
      (B * 300 + lam * 1600) * (S.card + K) * θ := by
    have : B * (300 * T.card * θ) + lam * (1600 * T.card * θ) =
        (B * 300 + lam * 1600) * T.card * θ := by ring
    rw [this]; gcongr
  have hpos : 0 < lam * (ε / 8) ^ 2 := by positivity
  linarith

end

end GT
end File_GT_U3S4e

open Finset KM
open scoped ComplexConjugate
open Classical
open GT in
theorem solution {p : ℕ} [NeZero p] {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) (hR1 : R 0 ≤ 1) (S : Finset (ZMod p))
    (W : (Fin 4 → ZMod p) → ℝ) {B : ℝ} (hW : ∀ q, |W q| ≤ B) (hW1 : ∀ q, W q ≤ 1)
    (A : Fin 4 → Finset (ZMod p)) (c0 : Fin 4 → ZMod p) {c3 ε mu : ℝ} {K : ℕ}
    (hc3 : 0 < c3) (hε : 0 < ε) (hmu : 0 < mu) (hQ0 : c3 ≤ QW R W S c0 0)
    (hmuε : 20 * mu ≤ c3 / 8 * (ε / 8) ^ 2 / 4) (hK : 1 + 20 * mu ≤ 20 * mu * K)
    (hθK : (B * 300 + c3 / 8 * 1600) * (S.card + K) * θ ≤ c3 / 8 * (ε / 8) ^ 2 / 4)
    (hsep : 7200 * (S.card + K) * θ ≤ (ε / 2) ^ 2)
    (herr : (350 * (S.card + K) + 13) * θ ≤ ε / 8) :
    ∃ (c : Fin 4 → ZMod p) (k : ℕ) (T : Finset (ZMod p)), S ⊆ T ∧ T.card ≤ S.card + k ∧
      k < K ∧ c3 / 2 ≤ QW R W T c (20 * k) ∧
      ∀ i, ∑ u, regP T (R (20 * k + lvl i)) (u - cent c i) *
        U2f T (R (20 * k + 10)) (R (20 * k + 11)) (bal R A T c (20 * k) i) u ≤ ε :=
  @GT.u3_step4 p _ R θ hR0 hRk hθ0 hθ1 hR1 S W B hW hW1 A c0 c3 ε mu K hc3 hε hmu hQ0 hmuε hK hθK hsep herr

