-- Prove2me | solution 1 for GT.loc_to_glob
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:47:19.749839+00:00
-- url     : https://prove2.me/submissions/c894b9f8-199f-4189-ae6c-72c62b159d82

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

/-- A representative of `x ∈ ℝ/ℤ` of absolute value `‖x‖`. -/
lemma exists_rep (x : UnitAddCircle) : ∃ s : ℝ, (s : UnitAddCircle) = x ∧ |s| = ‖x‖ ∧ |s| ≤ 1 / 2 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨t - round t, ?_, ?_, ?_⟩
  · rw [AddCircle.coe_sub]
    have : (((round t : ℤ) : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨round t, by simp⟩
    rw [this, sub_zero]
  · have := AddCircle.norm_eq (p := (1 : ℝ)) (x := t)
    simp only [inv_one, one_mul, mul_one] at this
    rw [show ‖(QuotientAddGroup.mk t : UnitAddCircle)‖ = ‖(t : UnitAddCircle)‖ from rfl, this]
  · exact abs_sub_round t

lemma norm_ec_sub_one_le (x : UnitAddCircle) : ‖ec x - 1‖ ≤ 2 * Real.pi * ‖x‖ := by
  obtain ⟨s, rfl, hs, -⟩ := exists_rep x
  rw [← hs]
  exact norm_toCircle_sub_one_le s

lemma four_norm_le (x : UnitAddCircle) : 4 * ‖x‖ ≤ ‖ec x - 1‖ := by
  obtain ⟨s, rfl, hs, hs2⟩ := exists_rep x
  rw [← hs, ec_coe, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hx0 : 0 ≤ Real.pi * |s| := by positivity
  have hx1 : Real.pi * |s| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hx0 hx1
  have e : 2 / Real.pi * (Real.pi * |s|) = 2 * |s| := by field_simp
  rw [e] at hsin
  have habs : |Real.sin (2 * Real.pi * s / 2)| = Real.sin (Real.pi * |s|) := by
    rw [show 2 * Real.pi * s / 2 = Real.pi * s by ring]
    rcases le_or_gt 0 s with h | h
    · have h1 : s ≤ 1 / 2 := le_trans (le_abs_self _) hs2
      rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos]))]
    · have h1 : -s ≤ 1 / 2 := le_trans (neg_le_abs _) hs2
      rw [abs_of_neg h, show Real.pi * s = -(Real.pi * -s) by ring, Real.sin_neg,
        abs_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos]))]
  rw [Real.norm_eq_abs, abs_mul, abs_two, habs]
  linarith

lemma norm_ec_sub_ec_le (x y : UnitAddCircle) : ‖ec x - ec y‖ ≤ 2 * Real.pi * ‖x - y‖ := by
  have : ec x - ec y = ec y * (ec (x - y) - 1) := by
    rw [mul_sub, mul_one, ← ec_add, add_sub_cancel]
  rw [this, norm_mul, norm_ec, one_mul]
  exact norm_ec_sub_one_le _

variable {N : ℕ} [NeZero N]

lemma ech_eq_ec (z : ZMod N) : ech z = ec (ZMod.toAddCircle z) := by
  rw [ech_eq_exp_sc, toAddCircle_eq_sc, ec_coe]

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

section File_GT_LocGlob
/-!
# Locally almost linear phases are globally almost linear (Green–Tao, Corollary 4.11)
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N] {S : Finset (ZMod N)}

lemma sum4_weights_eq_nest {P Q R T : ZMod N → ℝ} (F : ZMod N → ZMod N → ZMod N → ZMod N → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ((P a * Q b * R c * T d : ℝ) : ℂ) * F a b c d =
      ∑ a, (P a : ℂ) * ∑ b, (Q b : ℂ) * ∑ c, (R c : ℂ) * ∑ d, (T d : ℂ) * F a b c d := by
  simp only [mul_sum]
  push_cast
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => by ring

set_option maxHeartbeats 4000000 in
/-- **Corollary 4.11** of Green–Tao: a function on a shifted Bohr set whose second differences
are small (in terms of the dual norm) is close to a linear phase. -/
theorem loc_to_glob (hS : S.Nonempty) {ρ A : ℝ} (hρ : 0 < ρ) (hA : 1 ≤ A)
    (φ : ZMod N → UnitAddCircle) (n0 : ZMod N)
    (hφ : ∀ h k, h ∈ bohr S (ρ / 2) → k ∈ bohr S (ρ / 2) →
      ‖φ (n0 + h + k) - φ (n0 + h) - φ (n0 + k) + φ n0‖ ≤ A * snorm S h * snorm S k / ρ ^ 2) :
    ∃ ξ : ZMod N, ∀ h ∈ bohr S ρ,
      ‖φ (n0 + h) - φ n0 - ZMod.toAddCircle (ξ * h)‖ ≤
        10 ^ 9 * √A * (S.card : ℝ) ^ 4 * snorm S h / ρ := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = S.card := ⟨_, rfl⟩
  rw [← hd]
  have hd1 : 1 ≤ d := by rw [hd]; exact_mod_cast hS.card_pos
  have hsA : 1 ≤ √A := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hA
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ρ / √A := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos hρ (by linarith)
  have hrρ : r ≤ ρ := by rw [hr]; exact div_le_self hρ.le hsA
  have hr2 : r ^ 2 = ρ ^ 2 / A := by rw [hr, div_pow, Real.sq_sqrt (by linarith)]
  have hrinv : √A / ρ = 1 / r := by rw [hr]; field_simp
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ZMod N → UnitAddCircle, ∀ h, ψ h = φ (n0 + h) - φ n0 :=
    ⟨_, fun h => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ZMod N → ZMod N → UnitAddCircle, ∀ h k, D h k = ψ (h + k) - ψ h - ψ k :=
    ⟨_, fun h k => rfl⟩
  have hψD : ∀ h k, ψ (h + k) = ψ h + ψ k + D h k := by intro h k; rw [hD]; abel
  have hDb : ∀ h k, snorm S h ≤ r / 2 → snorm S k ≤ r / 2 →
      ‖D h k‖ ≤ snorm S h * snorm S k / r ^ 2 := by
    intro h k hh hk
    have e : D h k = φ (n0 + h + k) - φ (n0 + h) - φ (n0 + k) + φ n0 := by
      rw [hD, hψ, hψ, hψ, add_assoc]; abel
    rw [e]
    refine (hφ h k ((mem_bohr_iff_snorm (by positivity)).mpr (by linarith))
      ((mem_bohr_iff_snorm (by positivity)).mpr (by linarith))).trans (le_of_eq ?_)
    rw [hr2]; field_simp
  -- scales
  obtain ⟨ρ0, hρ0⟩ : ∃ x : ℝ, x = r / 100 := ⟨_, rfl⟩
  obtain ⟨ρ1, hρ1⟩ : ∃ x : ℝ, x = r / (10 ^ 7 * d ^ 3) := ⟨_, rfl⟩
  have hd3 : 1 ≤ d ^ 3 := one_le_pow₀ hd1
  have hρ0pos : 0 < ρ0 := by rw [hρ0]; positivity
  have hρ1pos : 0 < ρ1 := by rw [hρ1]; exact div_pos hr0 (by positivity)
  have hρ1r : ρ1 ≤ r / 10 ^ 7 := by
    rw [hρ1]; apply div_le_div_of_nonneg_left hr0.le (by norm_num); nlinarith
  have hρ0ρ1 : ρ0 * ρ1 / r ^ 2 ≤ 1 / 10 ^ 9 := by
    rw [div_le_iff₀ (by positivity)]
    calc ρ0 * ρ1 ≤ (r / 100) * (r / 10 ^ 7) := by
          rw [hρ0]; apply mul_le_mul_of_nonneg_left hρ1r (by positivity)
      _ = 1 / 10 ^ 9 * r ^ 2 := by ring
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  -- the function
  obtain ⟨f, hf⟩ : ∃ f : ZMod N → ℂ, ∀ x, f x = if x ∈ bohr S r then ec (ψ x) else 0 :=
    ⟨_, fun x => rfl⟩
  have hf1 : ∀ x, ‖f x‖ ≤ 1 := by
    intro x; rw [hf]; split_ifs <;> simp
  have hfin : ∀ x, snorm S x ≤ r → f x = ec (ψ x) := by
    intro x hx; rw [hf, if_pos ((mem_bohr_iff_snorm hr0.le).mpr hx)]
  have hsupp0 : ∀ x, regP S ρ0 x ≠ 0 → snorm S x ≤ ρ0 := fun x hx =>
    snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ0pos.le hx) hρ0pos.le
  have hsupp1 : ∀ x, regP S ρ1 x ≠ 0 → snorm S x ≤ ρ1 := fun x hx =>
    snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ1pos.le hx) hρ1pos.le
  have hρ0r : ρ0 + ρ1 ≤ r / 2 := by rw [hρ0]; linarith
  -- the local `U²` norm of `f` is large
  have hU2 : (1 / 2 : ℝ) ≤ ‖∑ h0, ∑ h0', ∑ h1, ∑ h1',
      ((regP S ρ0 h0 * regP S ρ0 h0' * regP S ρ1 h1 * regP S ρ1 h1' : ℝ) : ℂ) *
      (f (h0 + h1) * conj (f (h0 + h1')) * conj (f (h0' + h1)) * f (h0' + h1'))‖ := by
    rw [sum4_weights_eq_nest]
    have hD0 := regP_isDist S (ρ := ρ0) hρ0pos.le
    have hD1 := regP_isDist S (ρ := ρ1) hρ1pos.le
    have key : ∀ h0 h0' h1 h1', regP S ρ0 h0 ≠ 0 → regP S ρ0 h0' ≠ 0 → regP S ρ1 h1 ≠ 0 →
        regP S ρ1 h1' ≠ 0 →
        ‖f (h0 + h1) * conj (f (h0 + h1')) * conj (f (h0' + h1)) * f (h0' + h1') - 1‖ ≤ 1 / 2 := by
      intro h0 h0' h1 h1' a b c e
      have s0 := hsupp0 _ a; have s0' := hsupp0 _ b; have s1 := hsupp1 _ c; have s1' := hsupp1 _ e
      have hsum : ∀ x y, snorm S x ≤ ρ0 → snorm S y ≤ ρ1 → snorm S (x + y) ≤ r := fun x y hx hy =>
        (snorm_add_le _ _).trans (by linarith)
      rw [hfin _ (hsum _ _ s0 s1), hfin _ (hsum _ _ s0 s1'), hfin _ (hsum _ _ s0' s1),
        hfin _ (hsum _ _ s0' s1'), ← ec_neg, ← ec_neg, ← ec_add, ← ec_add, ← ec_add]
      have e2 : ψ (h0 + h1) + -ψ (h0 + h1') + -ψ (h0' + h1) + ψ (h0' + h1') =
          D h0 h1 - D h0 h1' - D h0' h1 + D h0' h1' := by
        rw [hψD, hψD, hψD, hψD]; abel
      rw [e2]
      refine (norm_ec_sub_one_le _).trans ?_
      have b1 : ∀ x y, snorm S x ≤ ρ0 → snorm S y ≤ ρ1 → ‖D x y‖ ≤ 1 / 10 ^ 9 := by
        intro x y hx hy
        refine (hDb x y (by linarith) (by linarith)).trans (le_trans ?_ hρ0ρ1)
        gcongr
        · exact snorm_nonneg _
      have := norm_add_le (D h0 h1 - D h0 h1' - D h0' h1) (D h0' h1')
      have := norm_sub_le (D h0 h1 - D h0 h1') (D h0' h1)
      have := norm_sub_le (D h0 h1) (D h0 h1')
      have := b1 _ _ s0 s1; have := b1 _ _ s0 s1'; have := b1 _ _ s0' s1; have := b1 _ _ s0' s1'
      nlinarith [Real.pi_pos]
    have hnest : ‖∑ a, (regP S ρ0 a : ℂ) * ∑ b, (regP S ρ0 b : ℂ) * ∑ c, (regP S ρ1 c : ℂ) *
        ∑ e, (regP S ρ1 e : ℂ) *
          (f (a + c) * conj (f (a + e)) * conj (f (b + c)) * f (b + e)) - 1‖ ≤ 1 / 2 :=
      norm_wavg_sub_le hD0.1 hD0.2 _ _ fun a ha => norm_wavg_sub_le hD0.1 hD0.2 _ _ fun b hb =>
        norm_wavg_sub_le hD1.1 hD1.2 _ _ fun c hc => norm_wavg_sub_le hD1.1 hD1.2 _ _ fun e he =>
          key a b c e ha hb hc he
    have := norm_sub_norm_le (1 : ℂ) (∑ a, (regP S ρ0 a : ℂ) * ∑ b, (regP S ρ0 b : ℂ) *
      ∑ c, (regP S ρ1 c : ℂ) * ∑ e, (regP S ρ1 e : ℂ) *
        (f (a + c) * conj (f (a + e)) * conj (f (b + c)) * f (b + e)))
    rw [norm_sub_rev] at this
    simp only [norm_one] at this
    linarith
  -- apply the local inverse `U²` theorem
  have hsep : 7200 * (S.card : ℝ) * ρ1 ≤ (1 / 2) ^ 2 * ρ0 := by
    rw [← hd, hρ1, hρ0]
    have hd0 : 0 < d := by linarith
    rw [show 7200 * d * (r / (10 ^ 7 * d ^ 3)) = 7200 * r / (10 ^ 7 * d ^ 2) by
      field_simp]
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ d ^ 2 := one_le_pow₀ hd1
    nlinarith
  obtain ⟨ξ, hξ⟩ := loc_u2_bohr (S := S) hρ1pos (by rw [hρ0]; linarith) hsep (by norm_num) f hf1
    hU2
  have hD0 := regP_isDist S (ρ := ρ0) hρ0pos.le
  have hD1 := regP_isDist S (ρ := ρ1) hρ1pos.le
  obtain ⟨n, hn0, hn⟩ := exists_pos_ge hD0.1 hD0.2 _ hξ
  have hsn := hsupp0 n hn0
  have hY : 1 / 2 ≤ ‖∑ n1, (regP S ρ1 n1 : ℂ) * f (n + n1) * ech (-(ξ * n1))‖ := by
    nlinarith [norm_nonneg (∑ n1, (regP S ρ1 n1 : ℂ) * f (n + n1) * ech (-(ξ * n1)))]
  obtain ⟨χ, hχ⟩ : ∃ χ : ZMod N → UnitAddCircle, ∀ x, χ x = ZMod.toAddCircle (ξ * x) :=
    ⟨_, fun _ => rfl⟩
  have hχadd : ∀ x y, χ (x + y) = χ x + χ y := by intro x y; rw [hχ, hχ, hχ, mul_add, map_add]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ZMod N → UnitAddCircle, ∀ x, Φ x = ψ x - χ x := ⟨_, fun _ => rfl⟩
  have hΦD : ∀ x y, Φ (x + y) = Φ x + Φ y + D x y := by
    intro x y; rw [hΦ, hΦ, hΦ, hψD, hχadd]; abel
  have hbD : ∀ x y, snorm S x ≤ ρ1 → snorm S y ≤ r / 2 →
      ‖D x y‖ ≤ ρ1 * snorm S y / r ^ 2 := by
    intro x y hx hy
    refine (hDb x y (by linarith) hy).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx (snorm_nonneg _))
      (by positivity)
  -- the correlation with a linear phase
  have hYZ : ‖(∑ n1, (regP S ρ1 n1 : ℂ) * f (n + n1) * ech (-(ξ * n1))) -
      ec (ψ n) * ∑ n1, (regP S ρ1 n1 : ℂ) * ec (Φ n1)‖ ≤ 1 / 4 := by
    have e : (∑ n1, (regP S ρ1 n1 : ℂ) * f (n + n1) * ech (-(ξ * n1))) -
        ec (ψ n) * ∑ n1, (regP S ρ1 n1 : ℂ) * ec (Φ n1) =
        ∑ n1, (regP S ρ1 n1 : ℂ) * (f (n + n1) * ech (-(ξ * n1)) - ec (ψ n) * ec (Φ n1)) := by
      rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring
    rw [e]
    refine norm_wavg_le hD1.1 hD1.2 _ fun n1 hn1 => ?_
    have s1 := hsupp1 n1 hn1
    rw [hfin _ ((snorm_add_le _ _).trans (by linarith)), ech_eq_ec, ← ec_add, ← ec_add]
    have e2 : ψ (n + n1) + ZMod.toAddCircle (-(ξ * n1)) = ψ n + Φ n1 + D n n1 := by
      rw [hψD, hΦ, hχ, map_neg]; abel
    rw [e2]
    refine (norm_ec_sub_ec_le _ _).trans ?_
    rw [show ψ n + Φ n1 + D n n1 - (ψ n + Φ n1) = D n n1 by abel]
    have : ‖D n n1‖ ≤ 1 / 10 ^ 9 := by
      refine (hDb n n1 (by linarith) (by linarith)).trans (le_trans ?_ hρ0ρ1)
      gcongr
      exact snorm_nonneg _
    have := mul_le_mul hpi this (norm_nonneg _) (by norm_num)
    linarith
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℂ, Z = ∑ n1, (regP S ρ1 n1 : ℂ) * ec (Φ n1) := ⟨_, rfl⟩
  rw [← hZdef] at hYZ
  have hZ : 1 / 4 ≤ ‖Z‖ := by
    have := norm_sub_norm_le (∑ n1, (regP S ρ1 n1 : ℂ) * f (n + n1) * ech (-(ξ * n1)))
      (ec (ψ n) * Z)
    rw [norm_mul, norm_ec, one_mul] at this
    linarith only [hY, hYZ, this]
  refine ⟨ξ, fun h hh => ?_⟩
  have hLHS : φ (n0 + h) - φ n0 - ZMod.toAddCircle (ξ * h) = Φ h := by rw [hΦ, hψ, hχ]
  rw [hLHS, show 10 ^ 9 * √A * d ^ 4 * snorm S h / ρ = 10 ^ 9 * d ^ 4 * snorm S h * (√A / ρ) by
    ring, hrinv]
  have hsh0 := snorm_nonneg (S := S) h
  by_cases hsmall : snorm S h ≤ ρ1 / 4
  · -- the main estimate
    have hshift := regP_shift (Γ := S) (Γ' := S) subset_rfl hρ1pos hsh0 (by linarith)
      (mem_bohr_snorm h) (B := 1) (fun x => ec (Φ x)) (fun x => by simp)
    have hZ' : ‖(∑ x, (regP S ρ1 x : ℂ) * ec (Φ (x + h))) - ec (Φ h) * Z‖ ≤
        2 * Real.pi * (ρ1 * snorm S h / r ^ 2) := by
      have e : (∑ x, (regP S ρ1 x : ℂ) * ec (Φ (x + h))) - ec (Φ h) * Z =
          ∑ x, (regP S ρ1 x : ℂ) * (ec (Φ (x + h)) - ec (Φ h) * ec (Φ x)) := by
        rw [hZdef, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring
      rw [e]
      refine norm_wavg_le hD1.1 hD1.2 _ fun x hx => ?_
      have s1 := hsupp1 x hx
      rw [← ec_add, hΦD]
      refine (norm_ec_sub_ec_le _ _).trans ?_
      rw [show Φ x + Φ h + D x h - (Φ h + Φ x) = D x h by abel]
      exact mul_le_mul_of_nonneg_left (hbD x h s1 (by linarith)) (by positivity)
    have hmain : ‖ec (Φ h) - 1‖ * ‖Z‖ ≤
        2 * Real.pi * (ρ1 * snorm S h / r ^ 2) + 1 * (50 * (S.card : ℝ) * snorm S h / ρ1) := by
      rw [← norm_mul, sub_mul, one_mul]
      have := norm_sub_le_norm_sub_add_norm_sub (ec (Φ h) * Z)
        (∑ x, (regP S ρ1 x : ℂ) * ec (Φ (x + h))) Z
      rw [norm_sub_rev] at hZ'
      have hs : ‖(∑ x, (regP S ρ1 x : ℂ) * ec (Φ (x + h))) - Z‖ ≤
          1 * (50 * (S.card : ℝ) * snorm S h / ρ1) := by
        rw [hZdef]; exact hshift
      linarith only [this, hZ', hs]
    have h4 := four_norm_le (Φ h)
    have hΦb : ‖Φ h‖ ≤ 2 * Real.pi * (ρ1 * snorm S h / r ^ 2) + 50 * d * snorm S h / ρ1 := by
      rw [← hd, one_mul] at hmain
      have hn0 : 0 ≤ ‖Φ h‖ := norm_nonneg _
      have a : ‖Φ h‖ ≤ 4 * ‖Φ h‖ * ‖Z‖ := by
        have := mul_le_mul_of_nonneg_left hZ hn0
        linarith only [this]
      have b : 4 * ‖Φ h‖ * ‖Z‖ ≤ ‖ec (Φ h) - 1‖ * ‖Z‖ :=
        mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      linarith only [a, b, hmain]
    refine hΦb.trans ?_
    have e1 : 50 * d * snorm S h / ρ1 = 5 * 10 ^ 8 * d ^ 4 * snorm S h * (1 / r) := by
      rw [hρ1]; field_simp; ring
    have e2 : 2 * Real.pi * (ρ1 * snorm S h / r ^ 2) ≤ 8 * snorm S h * (1 / r) := by
      rw [show 2 * Real.pi * (ρ1 * snorm S h / r ^ 2) = 2 * Real.pi * (ρ1 / r) * snorm S h * (1 / r)
        by field_simp]
      have : ρ1 / r ≤ 1 := by rw [div_le_one hr0]; linarith
      have : 2 * Real.pi * (ρ1 / r) ≤ 8 := by nlinarith [Real.pi_pos, div_nonneg hρ1pos.le hr0.le]
      have h1r : 0 ≤ snorm S h * (1 / r) := by positivity
      nlinarith
    rw [e1]
    have hd4 : 1 ≤ d ^ 4 := one_le_pow₀ hd1
    have h1r : 0 ≤ snorm S h * (1 / r) := by positivity
    nlinarith
  · -- trivial range
    push_neg at hsmall
    have h12 : ‖Φ h‖ ≤ 1 / 2 := by
      have := AddCircle.norm_le_half_period (1 : ℝ) (x := Φ h) one_ne_zero
      simpa using this
    refine h12.trans ?_
    have hρ1' : ρ1 * (1 / r) = 1 / (10 ^ 7 * d ^ 3) := by rw [hρ1]; field_simp
    have hd0 : 0 < d := by linarith
    have : 10 ^ 9 * d ^ 4 * (ρ1 / 4) * (1 / r) = 25 * d := by
      rw [show 10 ^ 9 * d ^ 4 * (ρ1 / 4) * (1 / r) = 10 ^ 9 * d ^ 4 / 4 * (ρ1 * (1 / r)) by ring,
        hρ1']
      field_simp; ring
    have hmono : 10 ^ 9 * d ^ 4 * (ρ1 / 4) * (1 / r) ≤ 10 ^ 9 * d ^ 4 * snorm S h * (1 / r) := by
      gcongr
    linarith

end

end GT
end File_GT_LocGlob

open Finset ComplexConjugate KM
open GT in
theorem solution {N : ℕ} [NeZero N] {S : Finset (ZMod N)} (hS : S.Nonempty) {ρ A : ℝ} (hρ : 0 < ρ) (hA : 1 ≤ A)
    (φ : ZMod N → UnitAddCircle) (n0 : ZMod N)
    (hφ : ∀ h k, h ∈ bohr S (ρ / 2) → k ∈ bohr S (ρ / 2) →
      ‖φ (n0 + h + k) - φ (n0 + h) - φ (n0 + k) + φ n0‖ ≤ A * snorm S h * snorm S k / ρ ^ 2) :
    ∃ ξ : ZMod N, ∀ h ∈ bohr S ρ,
      ‖φ (n0 + h) - φ n0 - ZMod.toAddCircle (ξ * h)‖ ≤
        10 ^ 9 * √A * (S.card : ℝ) ^ 4 * snorm S h / ρ :=
  @GT.loc_to_glob N _ S hS ρ A hρ hA φ n0 hφ

