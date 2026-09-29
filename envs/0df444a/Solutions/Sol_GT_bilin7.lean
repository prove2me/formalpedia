-- Prove2me | solution 1 for GT.bilin7
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:51:54.996756+00:00
-- url     : https://prove2.me/submissions/ff53e753-91b5-402c-8a9f-3951f352d15e

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

end avg

end

end GT
end File_GT_Prob

section File_GT_AddOn
/-!
# Local additivity on Bohr sets

`AddOn S R f` says that `f (x + y) = f x + f y` whenever `‖x‖_{S^⊥} + ‖y‖_{S^⊥} ≤ R`.
Locally linear maps on Bohr sets (and the partial maps of locally bilinear maps) are of this
form; we record how they act on integer combinations.
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p] {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M]

namespace AddOn

variable {R : ℝ} {f : ZMod p → M}

end AddOn

lemma snorm_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℤ) (x : ι → ZMod p) :
    snorm S (∑ i ∈ s, (c i : ZMod p) * x i) ≤ ∑ i ∈ s, |(c i : ℝ)| * snorm S (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, sum_insert hj]
    exact (snorm_add_le _ _).trans (add_le_add (snorm_intsmul_le _ _) ih)

end

end GT
end File_GT_AddOn

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

lemma gdet_nonneg {r : ℕ} (v : Fin r → E) : 0 ≤ gdet v :=
  (Matrix.posSemidef_gram ℝ v).det_nonneg

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

/-- Shearing the tail by multiples of the head does not change the Gram determinant. -/
lemma gdet_cons_shear {r : ℕ} (x : E) (w : Fin r → E) (c : Fin r → ℝ) :
    gdet (Fin.cons x (fun j => w j + c j • x) : Fin (r + 1) → E) =
      gdet (Fin.cons x w : Fin (r + 1) → E) := by
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    Matrix.of fun i j => Fin.cases (if j = 0 then 1 else 0)
      (fun i' => if j = 0 then c i' else if j = i'.succ then 1 else 0) i
  have hM : mixF M (Fin.cons x w) = Fin.cons x (fun j => w j + c j • x) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [mixF, M]
    · simp only [mixF, M, Matrix.of_apply, Fin.cases_succ, Fin.cons_succ, Fin.sum_univ_succ,
        Fin.cons_zero, if_true, Fin.succ_ne_zero, if_false]
      rw [Finset.sum_eq_single i']
      · simp [add_comm]
      · intro b _ hb; simp [Fin.succ_inj, hb]
      · simp
  have hdet : M.det = 1 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hz : ∀ j : Fin r, M 0 j.succ = 0 := fun j => by simp [M, Fin.succ_ne_zero]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have hsub : (M.submatrix Fin.succ (Fin.succAbove 0)) = 1 := by
      ext i j
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Fin.cases_succ, Fin.succAbove_zero,
        Fin.succ_ne_zero, if_false, Fin.succ_inj, Matrix.one_apply]
      split_ifs <;> simp_all [eq_comm]
    rw [hsub, Matrix.det_one]
    simp [M]
  rw [← hM, gdet_mixF, hdet]
  ring

/-- Adding a combination of the tail to the head does not change the Gram determinant. -/
lemma gdet_cons_add {r : ℕ} (y : E) (w : Fin r → E) (c : Fin r → ℝ) :
    gdet (Fin.cons (y + ∑ j, c j • w j) w : Fin (r + 1) → E) =
      gdet (Fin.cons y w : Fin (r + 1) → E) := by
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    Matrix.of fun i j => Fin.cases (Fin.cases 1 c j)
      (fun i' => if j = i'.succ then 1 else 0) i
  have hM : mixF M (Fin.cons y w) = Fin.cons (y + ∑ j, c j • w j) w := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [mixF, M, Fin.sum_univ_succ]
    · simp only [mixF, M, Matrix.of_apply, Fin.cases_succ, Fin.cons_succ]
      rw [Finset.sum_eq_single i'.succ]
      · simp
      · intro b _ hb; simp [hb]
      · simp
  have hdet : M.det = 1 := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hz : ∀ i : Fin r, M i.succ 0 = 0 := fun i => by
      simp [M, (Fin.succ_ne_zero i).symm]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have hsub : (M.submatrix (Fin.succAbove 0) Fin.succ) = 1 := by
      ext i j
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Fin.cases_succ, Fin.succAbove_zero,
        Fin.succ_inj, Matrix.one_apply]
      split_ifs <;> simp_all [eq_comm]
    rw [hsub, Matrix.det_one]
    simp [M]
  rw [← hM, gdet_mixF, hdet]
  ring

/-- Orthogonal decomposition of a vector with respect to the span of a finite family. -/
lemma exists_orth_decomp {r : ℕ} (x : E) (w : Fin r → E) :
    ∃ y : E, (∀ j, @inner ℝ E _ y (w j) = 0) ∧ ∃ c : Fin r → ℝ, x = y + ∑ j, c j • w j := by
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range w)
  haveI : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  refine ⟨x - K.starProjection x, fun j => ?_, ?_⟩
  · have h := K.sub_starProjection_mem_orthogonal x
    rw [Submodule.mem_orthogonal'] at h
    exact h _ (Submodule.subset_span ⟨j, rfl⟩)
  · have hm : K.starProjection x ∈ K := K.starProjection_apply_mem x
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hm
    exact ⟨c, by rw [hc]; abel⟩

lemma norm_le_of_orth_decomp {r : ℕ} {x y : E} {w : Fin r → E} {c : Fin r → ℝ}
    (hy : ∀ j, @inner ℝ E _ y (w j) = 0) (hx : x = y + ∑ j, c j • w j) : ‖y‖ ≤ ‖x‖ := by
  have horth : @inner ℝ E _ y (∑ j, c j • w j) = 0 := by
    rw [inner_sum]; simp [inner_smul_right, hy]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y (∑ j, c j • w j) horth
  rw [← hx] at this
  nlinarith [norm_nonneg x, norm_nonneg y, sq_nonneg ‖∑ j, c j • w j‖]

/-- Base times height: `det Gram(x, w) = ‖y‖² det Gram(w)` for the orthogonal component `y`. -/
lemma gdet_cons_eq {r : ℕ} {x y : E} {w : Fin r → E} {c : Fin r → ℝ}
    (hy : ∀ j, @inner ℝ E _ y (w j) = 0) (hx : x = y + ∑ j, c j • w j) :
    gdet (Fin.cons x w : Fin (r + 1) → E) = ‖y‖ ^ 2 * gdet w := by
  rw [hx, gdet_cons_add, gdet_cons_orth y w hy]

/-- **Hadamard's inequality**. -/
lemma gdet_le_prod : ∀ {r : ℕ} (v : Fin r → E), gdet v ≤ ∏ i, ‖v i‖ ^ 2
  | 0, v => by simp [gdet]
  | r + 1, v => by
    obtain ⟨y, hy, c, hx⟩ := exists_orth_decomp (v 0) (Fin.tail v)
    have hv : v = Fin.cons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
    rw [hv, gdet_cons_eq hy hx, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h1 := norm_le_of_orth_decomp hy hx
    have h2 := gdet_le_prod (Fin.tail v)
    have h3 := gdet_nonneg (Fin.tail v)
    have h4 : ‖y‖ ^ 2 ≤ ‖v 0‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    exact mul_le_mul h4 h2 h3 (by positivity)

/-- Gram determinant is invariant under permutations. -/
lemma gdet_comp_perm {r : ℕ} (v : Fin r → E) (σ : Equiv.Perm (Fin r)) :
    gdet (v ∘ σ) = gdet v := by
  unfold gdet
  have : Matrix.gram ℝ (v ∘ σ) = (Matrix.gram ℝ v).submatrix σ σ := by
    ext i j; simp [Matrix.gram_apply]
  rw [this, Matrix.det_submatrix_equiv_self]

/-- **Coordinate bound** (Cramer + Hadamard), for the index `0`. -/
lemma coord_bound_zero {r : ℕ} (v : Fin (r + 1) → E) (t : Fin (r + 1) → ℝ) :
    |t 0| * Real.sqrt (gdet v) ≤ ‖∑ j, t j • v j‖ * ∏ j : Fin r, ‖v j.succ‖ := by
  obtain ⟨y, hy, c, hx⟩ := exists_orth_decomp (v 0) (Fin.tail v)
  have hv : v = Fin.cons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
  have hg : gdet v = ‖y‖ ^ 2 * gdet (Fin.tail v) := by rw [hv, gdet_cons_eq hy hx]; simp
  have hsq : Real.sqrt (gdet v) = ‖y‖ * Real.sqrt (gdet (Fin.tail v)) := by
    rw [hg, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hhad : Real.sqrt (gdet (Fin.tail v)) ≤ ∏ j : Fin r, ‖v j.succ‖ := by
    rw [Real.sqrt_le_left (by positivity)]
    calc gdet (Fin.tail v) ≤ ∏ j, ‖Fin.tail v j‖ ^ 2 := gdet_le_prod _
      _ = (∏ j : Fin r, ‖v j.succ‖) ^ 2 := by rw [Finset.prod_pow]; rfl
  -- ⟪∑ t_j v_j, y⟫ = t 0 ‖y‖²
  have hinner : @inner ℝ E _ (∑ j, t j • v j) y = t 0 * ‖y‖ ^ 2 := by
    rw [sum_inner, Fin.sum_univ_succ]
    have hz : ∀ j : Fin r, @inner ℝ E _ (t j.succ • v j.succ) y = 0 := by
      intro j; rw [inner_smul_left, real_inner_comm]; simp only [mul_eq_zero]; right; exact hy j
    simp only [hz, Finset.sum_const_zero, add_zero, inner_smul_left, RCLike.conj_to_real]
    congr 1
    rw [hx, inner_add_left, real_inner_self_eq_norm_sq, sum_inner]
    simp [inner_smul_left, real_inner_comm, hy]
  have hcs : |t 0| * ‖y‖ ^ 2 ≤ ‖∑ j, t j • v j‖ * ‖y‖ := by
    have := abs_real_inner_le_norm (∑ j, t j • v j) y
    rw [hinner, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)] at this
    exact this
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | hpos
  · rw [hsq, ← h0]; simp; positivity
  · have hty : |t 0| * ‖y‖ ≤ ‖∑ j, t j • v j‖ := by
      have := hcs; rw [pow_two, ← mul_assoc] at this
      exact le_of_mul_le_mul_right this hpos
    rw [hsq, ← mul_assoc]
    exact mul_le_mul hty hhad (Real.sqrt_nonneg _) (norm_nonneg _)

end

end GT
end File_GT_Lattice

section File_GT_Vino
/-!
# Geometric sums and Vinogradov's lemma

Used in the proof of Proposition 4.9 (large local quadratic exponential sums).
-/

open Finset

namespace GT

noncomputable section

lemma norm_coe_real_le (s : ℝ) : ‖(s : UnitAddCircle)‖ ≤ |s| := QuotientAddGroup.norm_mk_le_norm

end

end GT
end File_GT_Vino

section File_GT_Unimod
/-!
# Completing a primitive integer vector to a unimodular matrix
-/

open Matrix

namespace GT

lemma vecMul_transvection_apply {n : ℕ} (m : Fin n → ℤ) {i j : Fin n} (c : ℤ) (k : Fin n) :
    (m ᵥ* transvection j i c) k = m k + if k = i then m j * c else 0 := by
  unfold transvection
  rw [Matrix.vecMul_add]
  simp only [Matrix.vecMul_one, Pi.add_apply]
  congr 1
  simp only [Matrix.vecMul, dotProduct, Matrix.single_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm h]

theorem exists_unimod_reduce {r : ℕ} :
    ∀ (N : ℕ) (m : Fin (r + 1) → ℤ), ∑ j, (m j).natAbs = N → Prim m →
      ∃ V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ, IsUnit V.det ∧ m ᵥ* V = Pi.single 0 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro m hN hm
  by_cases h : ∃ i j, i ≠ j ∧ m i ≠ 0 ∧ m j ≠ 0 ∧ |m j| ≤ |m i|
  · obtain ⟨i, j, hij, hi, hj, hle⟩ := h
    set c : ℤ := -(Int.sign (m i) * Int.sign (m j)) with hc
    set m' := m ᵥ* transvection j i c with hm'
    have hm'i : m' i = m i + m j * c := by rw [hm', vecMul_transvection_apply]; simp
    have hm'k : ∀ k, k ≠ i → m' k = m k := by
      intro k hk; rw [hm', vecMul_transvection_apply]; simp [hk]
    have habs : (m' i).natAbs + (m j).natAbs = (m i).natAbs := by
      rw [hm'i, hc]
      rcases lt_or_gt_of_ne hi with hi' | hi' <;> rcases lt_or_gt_of_ne hj with hj' | hj'
      · rw [Int.sign_eq_neg_one_of_neg hi', Int.sign_eq_neg_one_of_neg hj']
        rw [abs_of_neg hi', abs_of_neg hj'] at hle; omega
      · rw [Int.sign_eq_neg_one_of_neg hi', Int.sign_eq_one_of_pos hj']
        rw [abs_of_neg hi', abs_of_pos hj'] at hle; omega
      · rw [Int.sign_eq_one_of_pos hi', Int.sign_eq_neg_one_of_neg hj']
        rw [abs_of_pos hi', abs_of_neg hj'] at hle; omega
      · rw [Int.sign_eq_one_of_pos hi', Int.sign_eq_one_of_pos hj']
        rw [abs_of_pos hi', abs_of_pos hj'] at hle; omega
    have hsum : ∑ k, (m' k).natAbs + (m j).natAbs = N := by
      rw [← hN, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have : ∑ k ∈ Finset.univ.erase i, (m' k).natAbs = ∑ k ∈ Finset.univ.erase i, (m k).natAbs :=
        Finset.sum_congr rfl fun k hk => by rw [hm'k k (Finset.ne_of_mem_erase hk)]
      rw [this]; omega
    have hjpos : 0 < (m j).natAbs := Int.natAbs_pos.mpr hj
    have hprim : Prim m' := by
      intro q hq
      apply hm q
      intro k
      by_cases hk : k = i
      · subst hk
        have h1 := hq k
        have h2 := hq j
        rw [hm'i] at h1
        rw [hm'k j (Ne.symm hij)] at h2
        have : m k = (m k + m j * c) - m j * c := by ring
        rw [this]; exact dvd_sub h1 (dvd_mul_of_dvd_left h2 c)
      · rw [← hm'k k hk]; exact hq k
    obtain ⟨V', hV', hmV'⟩ := ih _ (by omega) m' rfl hprim
    refine ⟨transvection j i c * V', ?_, ?_⟩
    · rw [Matrix.det_mul, det_transvection_of_ne _ _ (Ne.symm hij), one_mul]; exact hV'
    · rw [← Matrix.vecMul_vecMul, ← hm', hmV']
  · push_neg at h
    have hne : ∃ i, m i ≠ 0 := by
      by_contra h0; push_neg at h0
      have := hm 0 (fun j => by rw [h0 j])
      exact not_isUnit_zero this
    obtain ⟨i, hi⟩ := hne
    have hzero : ∀ k, k ≠ i → m k = 0 := by
      intro k hk
      by_contra hk0
      rcases le_total |m k| |m i| with hle | hle
      · exact absurd hle (not_le.mpr (h i k (Ne.symm hk) hi hk0))
      · exact absurd hle (not_le.mpr (h k i hk hk0 hi))
    have hu : IsUnit (m i) := by
      apply hm (m i)
      intro k
      by_cases hk : k = i
      · rw [hk]
      · rw [hzero k hk]; exact dvd_zero _
    have hmsingle : m = Pi.single i (m i) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · rw [hzero k hk, Pi.single_eq_of_ne hk]
    have hsq : m i * m i = 1 := by
      rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num
    by_cases hi0 : i = 0
    · subst hi0
      refine ⟨m 0 • 1, ?_, ?_⟩
      · rw [Matrix.det_smul, Matrix.det_one, mul_one]
        exact (hu.pow _)
      · rw [Matrix.vecMul_smul, Matrix.vecMul_one, hmsingle]
        funext k
        by_cases hk : k = 0
        · subst hk; simp [hsq]
        · simp [Pi.single_eq_of_ne hk]
    · refine ⟨transvection i 0 1 * transvection 0 i (-1) * (m i • 1), ?_, ?_⟩
      · rw [Matrix.det_mul, Matrix.det_mul, det_transvection_of_ne _ _ hi0,
          det_transvection_of_ne _ _ (Ne.symm hi0), Matrix.det_smul, Matrix.det_one]
        simpa using hu
      · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_smul,
          Matrix.vecMul_one]
        funext k
        simp only [vecMul_transvection_apply, Pi.smul_apply, smul_eq_mul]
        rw [hmsingle]
        by_cases hk0 : k = 0
        · subst hk0
          have h0i : (0 : Fin (r + 1)) ≠ i := Ne.symm hi0
          simp [h0i, hsq]
        · by_cases hki : k = i
          · subst hki; simp [hk0]
          · simp [hk0, hki]

/-- A primitive integer vector is the first row of a unimodular integer matrix. -/
theorem exists_unimod_row {r : ℕ} {m : Fin (r + 1) → ℤ} (hm : Prim m) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ, IsUnit U.det ∧ U 0 = m := by
  obtain ⟨V, hV, hmV⟩ := exists_unimod_reduce _ m rfl hm
  refine ⟨V⁻¹, ?_, ?_⟩
  · exact Matrix.isUnit_nonsing_inv_det V hV
  · have h1 : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hV
    have : m ᵥ* V ᵥ* V⁻¹ = m := by rw [Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    rw [hmV, Matrix.single_one_vecMul] at this
    exact this

end GT
end File_GT_Unimod

section File_GT_Hermite
/-!
# Hermite reduction of lattice bases

Every lattice `⊕ ℤ u_i` (with `u` linearly independent) has a basis `b = M u`, `M ∈ GL_r(ℤ)`,
with `(∏ ‖b_i‖)² ≤ 2^{r²} det Gram(u)`.
-/

open Finset Matrix

namespace GT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma zmix_eq_mixF {r s : ℕ} (M : Matrix (Fin r) (Fin s) ℤ) (u : Fin s → E) :
    zmix M u = mixF (M.map (Int.cast : ℤ → ℝ)) u := rfl

lemma zvec_zmix {r s : ℕ} (m : Fin r → ℤ) (M : Matrix (Fin r) (Fin s) ℤ) (u : Fin s → E) :
    zvec m (zmix M u) = zvec (m ᵥ* M) u := by
  simp only [zvec, zmix, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul]
  push_cast
  rfl

lemma zmix_zmix {r s t : ℕ} (A : Matrix (Fin r) (Fin s) ℤ) (B : Matrix (Fin s) (Fin t) ℤ)
    (u : Fin t → E) : zmix A (zmix B u) = zmix (A * B) u := by
  funext i
  change zvec (A i) (zmix B u) = zvec ((A * B) i) u
  rw [zvec_zmix]
  rfl

lemma zvec_eq_zero {r : ℕ} {u : Fin r → E} (hu : LinearIndependent ℝ u) {m : Fin r → ℤ}
    (h : zvec m u = 0) : m = 0 := by
  have := (Fintype.linearIndependent_iff.mp hu) (fun j => (m j : ℝ)) h
  funext j; have := this j; try simp only at this
  exact_mod_cast this

lemma det_map_cast_sq {r : ℕ} {M : Matrix (Fin r) (Fin r) ℤ} (hM : IsUnit M.det) :
    (M.map (Int.cast : ℤ → ℝ)).det ^ 2 = 1 := by
  have h : (M.map (Int.cast : ℤ → ℝ)).det = ((M.det : ℤ) : ℝ) := by
    have := RingHom.map_det (Int.castRingHom ℝ) M
    simpa using this.symm
  rw [h]
  rcases Int.isUnit_iff.mp hM with h1 | h1 <;> rw [h1] <;> norm_num

lemma gdet_zmix_unimod {r : ℕ} {M : Matrix (Fin r) (Fin r) ℤ} (hM : IsUnit M.det)
    (u : Fin r → E) : gdet (zmix M u) = gdet u := by
  rw [zmix_eq_mixF, gdet_mixF, det_map_cast_sq hM, one_mul]

lemma linIndep_zmix_unimod {r : ℕ} {M : Matrix (Fin r) (Fin r) ℤ} (hM : IsUnit M.det)
    {u : Fin r → E} (hu : LinearIndependent ℝ u) : LinearIndependent ℝ (zmix M u) :=
  linearIndependent_of_gdet_ne_zero (by rw [gdet_zmix_unimod hM]; exact (gdet_pos hu).ne')

/-- Coordinate bound for an arbitrary index. -/
lemma coord_bound {r : ℕ} (v : Fin r → E) (t : Fin r → ℝ) (i : Fin r) :
    |t i| * Real.sqrt (gdet v) * ‖v i‖ ≤ ‖∑ j, t j • v j‖ * ∏ j, ‖v j‖ := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r =>
  set σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap 0 i
  have h := coord_bound_zero (v ∘ σ) (t ∘ σ)
  rw [gdet_comp_perm] at h
  have hsum : ∑ j, (t ∘ σ) j • (v ∘ σ) j = ∑ j, t j • v j :=
    Equiv.sum_comp σ (fun j => t j • v j)
  rw [hsum] at h
  have hprod : ∏ j, ‖v j‖ = ‖v i‖ * ∏ j : Fin r, ‖(v ∘ σ) j.succ‖ := by
    rw [← Equiv.prod_comp σ (fun j => ‖v j‖), Fin.prod_univ_succ]
    simp [σ]
  have hti : (t ∘ σ) 0 = t i := by simp [σ]
  rw [hti] at h
  rw [hprod]
  calc |t i| * Real.sqrt (gdet v) * ‖v i‖ ≤
        ‖∑ j, t j • v j‖ * (∏ j : Fin r, ‖(v ∘ σ) j.succ‖) * ‖v i‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

/-- Existence of a shortest non-zero lattice vector. -/
lemma exists_shortest {r : ℕ} {u : Fin (r + 1) → E} (hu : LinearIndependent ℝ u) :
    ∃ m : Fin (r + 1) → ℤ, m ≠ 0 ∧ ∀ m' : Fin (r + 1) → ℤ, m' ≠ 0 →
      ‖zvec m u‖ ≤ ‖zvec m' u‖ := by
  classical
  set R := ‖u 0‖
  have hg : 0 < Real.sqrt (gdet u) := Real.sqrt_pos.mpr (gdet_pos hu)
  have hune : ∀ i, 0 < ‖u i‖ := fun i => norm_pos_iff.mpr (hu.ne_zero i)
  set P := ∏ j, ‖u j‖
  -- a uniform bound on coordinates of short vectors
  set K : ℕ := ⌈R * P / (Real.sqrt (gdet u) * (univ.inf' univ_nonempty fun i => ‖u i‖))⌉₊
  have hinfpos : 0 < univ.inf' univ_nonempty fun i => ‖u i‖ := by
    rw [Finset.lt_inf'_iff]; exact fun i _ => hune i
  have hbox : ∀ m' : Fin (r + 1) → ℤ, ‖zvec m' u‖ ≤ R → ∀ i, |m' i| ≤ K := by
    intro m' hm' i
    have hc := coord_bound u (fun j => (m' j : ℝ)) i
    have hinf : (univ.inf' univ_nonempty fun i => ‖u i‖) ≤ ‖u i‖ :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have h1 : |(m' i : ℝ)| * (Real.sqrt (gdet u) * (univ.inf' univ_nonempty fun i => ‖u i‖)) ≤
        R * P := by
      calc |(m' i : ℝ)| * (Real.sqrt (gdet u) * (univ.inf' univ_nonempty fun i => ‖u i‖))
          ≤ |(m' i : ℝ)| * Real.sqrt (gdet u) * ‖u i‖ := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinf hg.le) (abs_nonneg _)
        _ ≤ ‖zvec m' u‖ * P := hc
        _ ≤ R * P := mul_le_mul_of_nonneg_right hm' (Finset.prod_nonneg fun j _ => norm_nonneg _)
    have h2 : |(m' i : ℝ)| ≤ K := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ (mul_pos hg hinfpos)]; exact h1
    exact_mod_cast h2
  set T : Finset (Fin (r + 1) → ℤ) :=
    (Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ)) K).filter
      (fun m' => m' ≠ 0 ∧ ‖zvec m' u‖ ≤ R)
  have he0 : (Pi.single 0 1 : Fin (r + 1) → ℤ) ∈ T := by
    have hn : ‖zvec (Pi.single 0 1 : Fin (r + 1) → ℤ) u‖ = R := by
      simp only [zvec, R]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · simp
    simp only [T, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨fun i => ?_, fun h => ?_, hn.le⟩
    · have := hbox _ hn.le i
      exact ⟨by linarith [neg_abs_le ((Pi.single 0 1 : Fin (r + 1) → ℤ) i)],
        le_trans (le_abs_self _) this⟩
    · have := congrFun h 0; simp at this
  obtain ⟨m, hmT, hmin⟩ := T.exists_min_image (fun m' => ‖zvec m' u‖) ⟨_, he0⟩
  simp only [T, Finset.mem_filter] at hmT
  refine ⟨m, hmT.2.1, fun m' hm' => ?_⟩
  by_cases hs : ‖zvec m' u‖ ≤ R
  · apply hmin
    simp only [T, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨fun i => ?_, hm', hs⟩
    have := hbox m' hs i
    exact ⟨by linarith [neg_abs_le (m' i)], le_trans (le_abs_self _) this⟩
  · push_neg at hs; linarith [hmT.2.2]

lemma prim_of_shortest {r : ℕ} {u : Fin (r + 1) → E} (hu : LinearIndependent ℝ u)
    {m : Fin (r + 1) → ℤ} (hm0 : m ≠ 0)
    (hmin : ∀ m' : Fin (r + 1) → ℤ, m' ≠ 0 → ‖zvec m u‖ ≤ ‖zvec m' u‖) : Prim m := by
  intro q hq
  by_contra hqu
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hm0; funext j; exact zero_dvd_iff.mp (hq j)
  have hq2 : 2 ≤ |q| := by
    rcases Int.isUnit_iff.not.mp hqu |> not_or.mp with ⟨h1, h2⟩
    rcases le_or_gt 0 q with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  choose m' hm' using hq
  have hm'0 : (m' : Fin (r + 1) → ℤ) ≠ 0 := by
    intro h; apply hm0; funext j; rw [hm' j, h]; simp
  have hz : zvec m u = (q : ℝ) • zvec m' u := by
    simp only [zvec, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hm' j]; push_cast; rfl
  have h1 := hmin m' hm'0
  rw [hz, norm_smul, Real.norm_eq_abs] at h1
  have hq2' : (2 : ℝ) ≤ |(q : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hq2
  have hnn := norm_nonneg (zvec m' u)
  have hzero : zvec m' u = 0 := by
    rw [← norm_eq_zero]; nlinarith
  exact hm'0 (zvec_eq_zero hu hzero)

/-- **Hermite reduction.** -/
theorem hermite : ∀ (r : ℕ) (u : Fin r → E), LinearIndependent ℝ u →
    ∃ M : Matrix (Fin r) (Fin r) ℤ, IsUnit M.det ∧
      (∏ i, ‖zmix M u i‖) ^ 2 ≤ 2 ^ (r ^ 2) * gdet u
  | 0, u, _ => ⟨1, by simp, by simp [gdet]⟩
  | r + 1, u, hu => by
    classical
    obtain ⟨m, hm0, hmin⟩ := exists_shortest hu
    have hprim := prim_of_shortest hu hm0 hmin
    obtain ⟨U, hU, hU0⟩ := exists_unimod_row hprim
    set u' := zmix U u with hu'def
    have hu' : LinearIndependent ℝ u' := linIndep_zmix_unimod hU hu
    have hgu' : gdet u' = gdet u := gdet_zmix_unimod hU u
    set b1 := u' 0 with hb1def
    have hb1 : b1 = zvec m u := by simp only [hb1def, hu'def, zmix, hU0]
    have hb1ne : b1 ≠ 0 := hu'.ne_zero 0
    have hb1pos : 0 < ‖b1‖ := norm_pos_iff.mpr hb1ne
    set s : Fin r → ℝ := fun j => @inner ℝ E _ (u' j.succ) b1 / ‖b1‖ ^ 2 with hsdef
    set y : Fin r → E := fun j => u' j.succ - s j • b1 with hydef
    have hy : ∀ j, @inner ℝ E _ b1 (y j) = 0 := by
      intro j
      simp only [hydef, hsdef, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      rw [real_inner_comm]
      field_simp
      ring
    have hu'cons : u' = Fin.cons b1 (fun j => y j + s j • b1) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hb1def]
      · simp [hydef]
    have hgdet : gdet u' = ‖b1‖ ^ 2 * gdet y := by
      rw [hu'cons, gdet_cons_shear, gdet_cons_orth _ _ hy]
    have hgpos := gdet_pos hu'
    have hy_li : LinearIndependent ℝ y := by
      apply linearIndependent_of_gdet_ne_zero
      intro h0; rw [hgdet, h0, mul_zero] at hgpos; exact lt_irrefl _ hgpos
    obtain ⟨N, hN, hNb⟩ := hermite r y hy_li
    set c := zmix N y with hcdef
    set σ : Fin r → ℝ := fun j => ∑ k, (N j k : ℝ) * s k with hσdef
    set t : Fin r → ℤ := fun j => round (σ j) with htdef
    set W : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ := Matrix.of fun i k =>
      Fin.cases ((Pi.single 0 1 : Fin (r + 1) → ℤ) k) (fun j => Fin.cases (-(t j)) (fun k' => N j k') k) i with hWdef
    set b := zmix W u' with hbdef
    have hb0 : b 0 = b1 := by
      simp only [hbdef, zmix, zvec, hWdef, Matrix.of_apply, Fin.cases_zero]
      rw [Finset.sum_eq_single 0]
      · simp [hb1def]
      · intro k _ hk; simp [Pi.single_eq_of_ne hk]
      · simp
    have hbs : ∀ j, b j.succ = c j + (σ j - t j) • b1 := by
      intro j
      simp only [hbdef, zmix, zvec, hWdef, Matrix.of_apply, Fin.cases_succ, Fin.sum_univ_succ,
        Fin.cases_zero, hcdef, hσdef]
      have : ∀ k : Fin r, u' k.succ = y k + s k • b1 := fun k => by simp [hydef]
      simp only [this, smul_add, Finset.sum_add_distrib, smul_smul, ← Finset.sum_smul,
        Finset.sum_mul]
      rw [← hb1def]
      push_cast
      rw [sub_smul]
      simp only [neg_smul]
      abel_nf
    have hWdet : W.det = N.det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      have hz : ∀ j : Fin r, W 0 j.succ = 0 := fun j => by
        simp [hWdef, Pi.single_eq_of_ne (Fin.succ_ne_zero j)]
      simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      have hsub : W.submatrix Fin.succ (Fin.succAbove 0) = N := by
        ext i j; simp [hWdef]
      rw [hsub]
      simp [hWdef]
    have hWU : IsUnit (W * U).det := by
      rw [Matrix.det_mul, hWdet]; exact hN.mul hU
    have hbW : zmix (W * U) u = b := by rw [hbdef, hu'def, zmix_zmix]
    refine ⟨W * U, hWU, ?_⟩
    rw [hbW]
    have hb_li : LinearIndependent ℝ b := by rw [← hbW]; exact linIndep_zmix_unimod hWU hu
    -- orthogonality of `c` to `b1`
    have hc_orth : ∀ j, @inner ℝ E _ b1 (c j) = 0 := by
      intro j
      simp only [hcdef, zmix, zvec, inner_sum, inner_smul_right, hy, mul_zero,
        Finset.sum_const_zero]
    have hbnorm : ∀ j : Fin r, ‖b j.succ‖ ^ 2 = ‖c j‖ ^ 2 + (σ j - t j) ^ 2 * ‖b1‖ ^ 2 := by
      intro j
      rw [hbs j]
      have h0 : @inner ℝ E _ (c j) ((σ j - t j) • b1) = 0 := by
        rw [inner_smul_right, real_inner_comm, hc_orth j, mul_zero]
      rw [norm_add_sq_real, h0, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hfrac : ∀ j : Fin r, (σ j - t j) ^ 2 ≤ 1 / 4 := by
      intro j
      have := abs_sub_round (σ j)
      have h2 : |σ j - (t j : ℝ)| ≤ 1 / 2 := by simpa [htdef] using this
      nlinarith [abs_nonneg (σ j - (t j : ℝ)), sq_abs (σ j - (t j : ℝ))]
    have hshort : ∀ j : Fin r, ‖b1‖ ≤ ‖b j.succ‖ := by
      intro j
      have hne : (W * U) j.succ ≠ 0 := by
        intro h
        apply hb_li.ne_zero j.succ
        rw [← hbW]; simp [zmix, zvec, h]
      have := hmin _ hne
      rw [← hb1] at this
      have e : zvec ((W * U) j.succ) u = b j.succ := by rw [← hbW]; rfl
      rwa [e] at this
    have hbj : ∀ j : Fin r, ‖b j.succ‖ ^ 2 ≤ 4 / 3 * ‖c j‖ ^ 2 := by
      intro j
      have h1 := hbnorm j
      have h2 := hfrac j
      have h3 := hshort j
      have h4 : ‖b1‖ ^ 2 ≤ ‖b j.succ‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      have h5 : (σ j - t j) ^ 2 * ‖b1‖ ^ 2 ≤ 1 / 4 * ‖b1‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      nlinarith
    have hprod : (∏ i, ‖b i‖) ^ 2 = ‖b1‖ ^ 2 * ∏ j : Fin r, ‖b j.succ‖ ^ 2 := by
      rw [Fin.prod_univ_succ, mul_pow, hb0, Finset.prod_pow]
    have hprod2 : ∏ j : Fin r, ‖b j.succ‖ ^ 2 ≤ (4 / 3) ^ r * (∏ j, ‖c j‖) ^ 2 := by
      calc ∏ j : Fin r, ‖b j.succ‖ ^ 2 ≤ ∏ j : Fin r, (4 / 3 * ‖c j‖ ^ 2) :=
            Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => hbj j)
        _ = (4 / 3) ^ r * (∏ j, ‖c j‖) ^ 2 := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              Finset.prod_pow]
    have hgy := gdet_nonneg y
    have h43 : (4 / 3 : ℝ) ^ r * 2 ^ (r ^ 2) ≤ 2 ^ ((r + 1) ^ 2) := by
      have e : (2 : ℝ) ^ ((r + 1) ^ 2) = 2 ^ (r ^ 2) * (2 ^ r * 2 ^ (r + 1)) := by
        rw [← pow_add, ← pow_add]; ring_nf
      rw [e]
      have : (4 / 3 : ℝ) ^ r ≤ 2 ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
      have h1 : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
      have h2 : (0 : ℝ) < 2 ^ (r ^ 2) := by positivity
      calc (4 / 3 : ℝ) ^ r * 2 ^ (r ^ 2) ≤ 2 ^ r * 2 ^ (r ^ 2) :=
            mul_le_mul_of_nonneg_right this h2.le
        _ ≤ 2 ^ r * 2 ^ (r ^ 2) * 2 ^ (r + 1) :=
            le_mul_of_one_le_right (by positivity) h1
        _ = 2 ^ (r ^ 2) * (2 ^ r * 2 ^ (r + 1)) := by ring
    rw [hprod, ← hgu', hgdet]
    calc ‖b1‖ ^ 2 * ∏ j : Fin r, ‖b j.succ‖ ^ 2
        ≤ ‖b1‖ ^ 2 * ((4 / 3) ^ r * (2 ^ (r ^ 2) * gdet y)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hprod2.trans (mul_le_mul_of_nonneg_left hNb (by positivity))
      _ = ((4 / 3) ^ r * 2 ^ (r ^ 2)) * (‖b1‖ ^ 2 * gdet y) := by ring
      _ ≤ 2 ^ ((r + 1) ^ 2) * (‖b1‖ ^ 2 * gdet y) :=
          mul_le_mul_of_nonneg_right h43 (by positivity)

end

end GT
end File_GT_Hermite

section File_GT_BohrBasis
/-!
# Bases of Bohr sets (Green–Tao, Lemma 4.7 / Corollary 4.8)

For a non-degenerate `S ⊆ ℤ/pℤ` with `|S| = d` we find `a_1, …, a_d ∈ ℤ/pℤ` and lengths
`ℓ_i > 0` with `‖a_i‖_{S^⊥} ≤ ℓ_i` such that every `x` is `∑ n_i a_i` with
`|n_i| ℓ_i ≤ 2^{d²} d ‖x‖_{S^⊥}`.  The lattice `Γ = ℤ^S + ℤ (s/p)_{s ∈ S}` is given an explicit
basis, which is then Hermite-reduced.
-/

open Finset Matrix KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- Abstract step: a lattice basis compatible with `ℤ/pℤ` yields a Bohr set basis. -/
theorem basis_of_lattice {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} {u : Fin d → E} (hu : LinearIndependent ℝ u) (a : Fin d → ZMod p)
    (S : Finset (ZMod p)) (R : ZMod p → ℝ)
    (h2 : ∀ m : Fin d → ℤ, snorm S (∑ j, (m j : ZMod p) * a j) ≤ ‖zvec m u‖)
    (h3 : ∀ x, ∃ m : Fin d → ℤ, ∑ j, (m j : ZMod p) * a j = x ∧ ‖zvec m u‖ ≤ R x)
    (h4 : ∀ m : Fin d → ℤ, ∑ j, (m j : ZMod p) * a j = 0 → ‖zvec m u‖ < 1 → m = 0) :
    ∃ (a' : Fin d → ZMod p) (ℓ : Fin d → ℝ), (∀ i, 0 < ℓ i) ∧ (∀ i, snorm S (a' i) ≤ ℓ i) ∧
      (∀ x, ∃ n : Fin d → ℤ, x = ∑ i, (n i : ZMod p) * a' i ∧
        ∀ i, |(n i : ℝ)| * ℓ i ≤ 2 ^ (d ^ 2) * R x) ∧
      ∀ k : Fin d → ℤ, ∑ i, (k i : ZMod p) * a' i = 0 → ∑ i, |(k i : ℝ)| * ℓ i < 1 → k = 0 := by
  obtain ⟨M, hM, hred⟩ := hermite d u hu
  obtain ⟨w, hw⟩ : ∃ w, w = zmix M u := ⟨_, rfl⟩
  have hwli : LinearIndependent ℝ w := by rw [hw]; exact linIndep_zmix_unimod hM hu
  have hgw : gdet w = gdet u := by rw [hw]; exact gdet_zmix_unimod hM u
  have hg0 : 0 < gdet w := gdet_pos hwli
  refine ⟨fun i => ∑ j, (M i j : ZMod p) * a j, fun i => ‖w i‖,
    fun i => norm_pos_iff.2 (hwli.ne_zero i), fun i => ?_, fun x => ?_, fun k hk hkl => ?_⟩
  · have := h2 (M i); rw [hw]; exact this
  · obtain ⟨m, hm, hmR⟩ := h3 x
    obtain ⟨n, hn⟩ : ∃ n : Fin d → ℤ, n = m ᵥ* M⁻¹ := ⟨_, rfl⟩
    have hnM : n ᵥ* M = m := by
      rw [hn, vecMul_vecMul, nonsing_inv_mul _ hM, vecMul_one]
    have hzv : zvec n w = zvec m u := by rw [hw, zvec_zmix, hnM]
    refine ⟨n, ?_, fun i => ?_⟩
    · rw [← hm, ← hnM]
      simp only [vecMul, dotProduct, Int.cast_sum, Int.cast_mul, sum_mul, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
    · have hc := coord_bound w (fun j => (n j : ℝ)) i
      have hsum : ∑ j, (n j : ℝ) • w j = zvec n w := rfl
      rw [hsum, hzv] at hc
      have hprod : ∏ j, ‖w j‖ ≤ 2 ^ (d ^ 2) * Real.sqrt (gdet w) := by
        have h1 : (∏ j, ‖w j‖) ^ 2 ≤ (2 ^ (d ^ 2) * Real.sqrt (gdet w)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hg0.le, hgw]
          rw [← hw] at hred
          refine hred.trans (mul_le_mul_of_nonneg_right ?_ (gdet_nonneg u))
          have : (1 : ℝ) ≤ 2 ^ (d ^ 2) := one_le_pow₀ (by norm_num)
          nlinarith
        exact (pow_le_pow_iff_left₀ (prod_nonneg fun j _ => norm_nonneg _)
          (by positivity) two_ne_zero).1 h1
      have hs0 : 0 < Real.sqrt (gdet w) := Real.sqrt_pos.2 hg0
      have h4 : |(n i : ℝ)| * Real.sqrt (gdet w) * ‖w i‖ ≤
          R x * (2 ^ (d ^ 2) * Real.sqrt (gdet w)) := by
        refine hc.trans ?_
        have hR : 0 ≤ ‖zvec m u‖ := norm_nonneg _
        exact mul_le_mul hmR hprod (prod_nonneg fun j _ => norm_nonneg _) (hR.trans hmR)
      have e : |(n i : ℝ)| * Real.sqrt (gdet w) * ‖w i‖ =
          (|(n i : ℝ)| * ‖w i‖) * Real.sqrt (gdet w) := by ring
      rw [e, show R x * (2 ^ (d ^ 2) * Real.sqrt (gdet w)) = (2 ^ (d ^ 2) * R x) *
        Real.sqrt (gdet w) by ring] at h4
      exact le_of_mul_le_mul_right h4 hs0
  · have hsumk : ∑ j, ((k ᵥ* M) j : ZMod p) * a j = 0 := by
      rw [← hk]
      simp only [vecMul, dotProduct, Int.cast_sum, Int.cast_mul, sum_mul, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
    have hnorm : ‖zvec (k ᵥ* M) u‖ < 1 := by
      have e : zvec (k ᵥ* M) u = zvec k w := by rw [hw, zvec_zmix]
      rw [e]
      refine lt_of_le_of_lt ?_ hkl
      unfold zvec
      refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
      rw [norm_smul, Real.norm_eq_abs]
    have h0 := h4 _ hsumk hnorm
    have : k = (k ᵥ* M) ᵥ* M⁻¹ := by
      rw [vecMul_vecMul, mul_nonsing_inv _ hM, vecMul_one]
    rw [this, h0, zero_vecMul]

lemma coe_intCast_real_eq_zero (n : ℤ) : (((n : ℝ)) : UnitAddCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨n, by simp⟩

/-- **Bohr set basis** (Corollary 4.8, with Hermite reduction in place of John's theorem). -/
theorem bohr_basis (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) :
    ∃ (a : Fin S.card → ZMod p) (ℓ : Fin S.card → ℝ), (∀ i, 0 < ℓ i) ∧
      (∀ i, snorm S (a i) ≤ ℓ i) ∧
      (∀ x, ∃ n : Fin S.card → ℤ, x = ∑ i, (n i : ZMod p) * a i ∧
        ∀ i, |(n i : ℝ)| * ℓ i ≤ 2 ^ (S.card ^ 2) * (S.card * snorm S x)) ∧
      ∀ k : Fin S.card → ℤ, ∑ i, (k i : ZMod p) * a i = 0 → ∑ i, |(k i : ℝ)| * ℓ i < 1 →
        k = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd⟩ : ∃ d, d = S.card := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : S ≃ Fin S.card, e = S.equivFin := ⟨_, rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : Fin S.card → ZMod p, sv = fun i => ((e.symm i : S) : ZMod p) :=
    ⟨_, rfl⟩
  have hsvS : ∀ i, sv i ∈ S := fun i => by rw [hsv]; exact (e.symm i).2
  have hsvsurj : ∀ s ∈ S, ∃ i, sv i = s := fun s hs => ⟨e ⟨s, hs⟩, by rw [hsv]; simp⟩
  obtain ⟨s0, hs0S, hs0⟩ := hS
  obtain ⟨i0, hi0⟩ := hsvsurj s0 hs0S
  obtain ⟨t, ht⟩ : ∃ t : ZMod p, t = (sv i0)⁻¹ := ⟨_, rfl⟩
  have hst : sv i0 * t = 1 := by rw [ht, hi0]; exact mul_inv_cancel₀ hs0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨xv, hxv⟩ : ∃ xv : Fin S.card → ℝ, xv = fun i => ((sv i * t).val : ℝ) / p := ⟨_, rfl⟩
  have hxv0 : xv i0 = 1 / p := by
    rw [hxv]; simp only; rw [hst, ZMod.val_one]; simp
  have hxvc : ∀ i, ((xv i : ℝ) : UnitAddCircle) = ZMod.toAddCircle (sv i * t) := by
    intro i; rw [hxv, ZMod.toAddCircle_apply]
  obtain ⟨u, hu⟩ : ∃ u : Fin S.card → EuclideanSpace ℝ (Fin S.card),
      u = fun j => if j = i0 then WithLp.toLp 2 xv else EuclideanSpace.single j 1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin S.card → ZMod p, a = fun j => if j = i0 then t else 0 := ⟨_, rfl⟩
  -- coordinates of a real combination
  have hcoord : ∀ (c : Fin S.card → ℝ) (i : Fin S.card),
      (∑ j, c j • u j).ofLp i = c i0 * xv i + if i = i0 then 0 else c i := by
    intro c i
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hu]
    have : ∀ j, c j * (if j = i0 then WithLp.toLp 2 xv else EuclideanSpace.single j (1 : ℝ)).ofLp i
        = (if j = i0 then c i0 * xv i else 0) + (if j = i then (if i = i0 then 0 else c i) else 0) := by
      intro j
      by_cases hj : j = i0
      · subst hj; by_cases hji : j = i
        · subst hji; simp
        · simp [hji, Ne.symm hji, EuclideanSpace.single_apply]
      · by_cases hji : j = i
        · subst hji; simp [hj, EuclideanSpace.single_apply]
        · simp [hj, hji, Ne.symm hji, EuclideanSpace.single_apply]
    rw [sum_congr rfl fun j _ => this j, sum_add_distrib, sum_ite_eq', sum_ite_eq']
    simp
  have hli : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : c i0 = 0 := by
      have := hcoord c i0
      rw [hc, hxv0] at this
      simp at this
      rcases this with h | h
      · exact h
      · exact absurd h (by first | exact hp0.ne' | exact NeZero.ne p | positivity)
    intro i
    by_cases hi : i = i0
    · rw [hi]; exact h0
    · have := hcoord c i
      rw [hc, h0] at this
      simp [hi] at this
      exact this.symm
  -- the key compatibility property
  have hP : ∀ (m : Fin S.card → ℤ) (i : Fin S.card), (((zvec m u).ofLp i : ℝ) : UnitAddCircle) =
      ZMod.toAddCircle (sv i * ∑ j, (m j : ZMod p) * a j) := by
    intro m i
    have hz : zvec m u = ∑ j, (m j : ℝ) • u j := rfl
    rw [hz, hcoord]
    have hint : ((if i = i0 then 0 else (m i : ℝ)) : ℝ) = ((if i = i0 then 0 else m i : ℤ) : ℝ) := by
      split_ifs <;> simp
    rw [hint, AddCircle.coe_add, coe_intCast_real_eq_zero, add_zero]
    have hsum : ∑ j, (m j : ZMod p) * a j = (m i0 : ZMod p) * t := by
      rw [ha]; simp
    rw [hsum, show sv i * ((m i0 : ZMod p) * t) = (m i0) • (sv i * t) by
      rw [zsmul_eq_mul]; ring, map_zsmul, ← hxvc, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  have H2 : ∀ m : Fin S.card → ℤ, snorm S (∑ j, (m j : ZMod p) * a j) ≤ ‖zvec m u‖ := by
    intro m
    rw [snorm_le_iff (norm_nonneg _)]
    intro s hs
    obtain ⟨i, rfl⟩ := hsvsurj s hs
    rw [cn, ← hP]
    exact (norm_coe_real_le _).trans (by
      have := PiLp.norm_apply_le (zvec m u) i
      rwa [Real.norm_eq_abs] at this)
  have H3 : ∀ x, ∃ m : Fin S.card → ℤ, ∑ j, (m j : ZMod p) * a j = x ∧
      ‖zvec m u‖ ≤ S.card * snorm S x := by
    intro x
    obtain ⟨z, hz⟩ : ∃ z : Fin S.card → ℝ, z = fun i => sc (sv i * x) := ⟨_, rfl⟩
    have hzc : ∀ i, ((z i : ℝ) : UnitAddCircle) = ZMod.toAddCircle (sv i * x) := by
      intro i; rw [hz, toAddCircle_eq_sc]
    obtain ⟨m0, hm0⟩ : ∃ m0 : ℤ, m0 = ((sv i0 * x).val : ℤ) -
        p * round (((sv i0 * x).val : ℝ) / p) := ⟨_, rfl⟩
    have hm0r : (m0 : ℝ) = p * z i0 := by
      rw [hm0, hz]; simp only [sc]; push_cast; field_simp
    have hm0z : (m0 : ZMod p) = sv i0 * x := by
      rw [hm0]; push_cast; rw [ZMod.natCast_self, zero_mul, sub_zero, ZMod.natCast_zmod_val]
    have hex : ∀ i, ∃ n : ℤ, (i ≠ i0 → (n : ℝ) = z i - m0 * xv i) ∧ (i = i0 → n = m0) := by
      intro i
      by_cases hi : i = i0
      · exact ⟨m0, fun h => absurd hi h, fun _ => rfl⟩
      · have h0 : ((z i - m0 * xv i : ℝ) : UnitAddCircle) = 0 := by
          rw [AddCircle.coe_sub, hzc, show (m0 : ℝ) * xv i = ((m0 • xv i : ℝ)) by
            rw [zsmul_eq_mul], AddCircle.coe_zsmul, hxvc, ← map_zsmul, ← map_sub, zsmul_eq_mul,
            hm0z, show sv i * x - sv i0 * x * (sv i * t) = sv i * x * (1 - sv i0 * t) by ring,
            hst, sub_self, mul_zero, map_zero]
        obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h0
        exact ⟨n, fun _ => by rw [← hn]; simp, fun h => absurd h hi⟩
    choose m hm using hex
    refine ⟨m, ?_, ?_⟩
    · have hsum : ∑ j, (m j : ZMod p) * a j = (m i0 : ZMod p) * t := by
        rw [ha]; simp
      rw [hsum, (hm i0).2 rfl, hm0z, mul_assoc, mul_comm x, ← mul_assoc, hst, one_mul]
    · have hzv : zvec m u = WithLp.toLp 2 z := by
        ext i
        have hz' : zvec m u = ∑ j, (m j : ℝ) • u j := rfl
        rw [hz', hcoord, (hm i0).2 rfl]
        simp only [PiLp.toLp_apply]
        by_cases hi : i = i0
        · subst hi; rw [if_pos rfl, add_zero, hxv0, hm0r]; field_simp
        · rw [if_neg hi, (hm i).1 hi]; ring
      rw [hzv, EuclideanSpace.norm_eq]
      have hzi : ∀ i, ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin S.card)).ofLp i‖ ≤ snorm S x := by
        intro i
        simp only [PiLp.toLp_apply, Real.norm_eq_abs, hz, ← cn_eq_abs_sc]
        exact cn_le_snorm (hsvS i) x
      have hsn := snorm_nonneg (S := S) x
      have hsq : ∑ i, ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin S.card)).ofLp i‖ ^ 2 ≤
          ((S.card : ℝ) * snorm S x) ^ 2 := by
        calc _ ≤ ∑ _i : Fin S.card, snorm S x ^ 2 :=
              sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hzi i) 2
          _ = S.card * snorm S x ^ 2 := by simp
          _ ≤ _ := by
              rw [mul_pow]
              have : (S.card : ℝ) ≤ (S.card : ℝ) ^ 2 := by
                rcases Nat.eq_zero_or_pos S.card with h | h
                · rw [h]; simp
                · have : (1 : ℝ) ≤ S.card := by exact_mod_cast h
                  nlinarith
              exact mul_le_mul_of_nonneg_right this (by positivity)
      calc _ ≤ Real.sqrt (((S.card : ℝ) * snorm S x) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = _ := Real.sqrt_sq (by positivity)
  have H4 : ∀ m : Fin S.card → ℤ, ∑ j, (m j : ZMod p) * a j = 0 → ‖zvec m u‖ < 1 → m = 0 := by
    intro m hm0 hm1
    have hz0 : zvec m u = 0 := by
      ext i
      have hPi := hP m i
      rw [hm0, mul_zero, map_zero] at hPi
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 hPi
      have hle : |(zvec m u).ofLp i| < 1 := by
        have := PiLp.norm_apply_le (zvec m u) i
        rw [Real.norm_eq_abs] at this
        linarith
      rw [← hn, zsmul_eq_mul, mul_one] at hle ⊢
      have : n = 0 := by
        have h2 := abs_lt.mp hle
        have h3 : 0 < n + 1 := by
          have h5 : (0 : ℝ) < (n : ℝ) + 1 := by linarith [h2.1]
          exact_mod_cast h5
        have h4 : n < 1 := by exact_mod_cast h2.2
        omega
      simp [this]
    have := (Fintype.linearIndependent_iff.1 hli) (fun j => (m j : ℝ)) hz0
    funext j
    have hj : ((m j : ℤ) : ℝ) = 0 := this j
    simpa using hj
  exact basis_of_lattice hli a S (fun x => S.card * snorm S x) H2 H3 H4

end

end GT
end File_GT_BohrBasis

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

section File_GT_U3S8a
/-!
# Local inverse `U³`, seventh step: a locally bilinear form

From a frequency function `ξ''` which is `100%` approximately linear on a Bohr set,
in the sense that every `μ(x,y) = ξ''(x+y) - ξ''(x) - ξ''(y)` is `Good`, we build a map
`Ξ : ZMod p → ZMod p → ℝ/ℤ` which is exactly additive in each variable on a small Bohr set and
close to `(x, m) ↦ ξ''(x) m / p`.

We avoid the lattice projections of the paper.  Real lifts `c(x,y)(m)` of `μ(x,y) m / p` form an
exact cocycle; averaging in the last variable gives `F₁` such that
`G_m(x) = ξ''(x) m / p + F₁(x)(m)` is additive up to an error proportional to the `T^⊥`-norm of
the increment.  Then `Ξ(n, m) = Σ_i x_i(n) G_m(a_i)`, with `x_i(n)` the coordinates of `n` in a
Bohr basis, is exactly bilinear, and a telescoping argument along the coordinates shows that it is
close to `G_m(n)`.
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Real lifts -/

/-- The signed representative of a point of `ℝ/ℤ`. -/
def rl (x : UnitAddCircle) : ℝ := Classical.choose (exists_rep x)

lemma rl_coe (x : UnitAddCircle) : ((rl x : ℝ) : UnitAddCircle) = x :=
  (Classical.choose_spec (exists_rep x)).1

lemma abs_rl (x : UnitAddCircle) : |rl x| = ‖x‖ :=
  (Classical.choose_spec (exists_rep x)).2.1

lemma norm_coe_le_abs (u : ℝ) : ‖(u : UnitAddCircle)‖ ≤ |u| := by
  have := AddCircle.norm_eq (p := (1 : ℝ)) (x := u)
  simp only [inv_one, one_mul, mul_one] at this
  rw [this]
  simpa using round_le u 0

lemma eq_zero_of_coe_eq_zero {u : ℝ} (h : (u : UnitAddCircle) = 0) (hu : |u| < 1) : u = 0 := by
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, rfl⟩ := h
  rw [zsmul_one] at hu ⊢
  have : |n| < 1 := by exact_mod_cast (show (|(n : ℝ)|) < 1 from hu)
  have : n = 0 := by rw [abs_lt] at this; omega
  simp [this]

lemma lift_add {u v w : ℝ} (h : (w : UnitAddCircle) = u + v) (hs : |u| + |v| + |w| < 1) :
    w = u + v := by
  have e : ((w - u - v : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_sub, h]; abel
  have hb : |w - u - v| < 1 := by
    calc |w - u - v| ≤ |w - u| + |v| := abs_sub _ _
      _ ≤ |w| + |u| + |v| := by linarith [abs_sub w u]
      _ < 1 := by linarith
  linarith [eq_zero_of_coe_eq_zero e hb]

/-! ### The cocycle and its real lift -/

/-- The cocycle of `ξ''`. -/
def mu2 (ξ'' : ZMod p → ZMod p) (x y : ZMod p) : ZMod p := ξ'' (x + y) - ξ'' x - ξ'' y

/-- The real lift of `μ(x,y) m / p`. -/
def cL (ξ'' : ZMod p → ZMod p) (x y m : ZMod p) : ℝ := rl (ZMod.toAddCircle (mu2 ξ'' x y * m))

lemma coe_cL (ξ'' : ZMod p → ZMod p) (x y m : ZMod p) :
    ((cL ξ'' x y m : ℝ) : UnitAddCircle) = ZMod.toAddCircle (mu2 ξ'' x y * m) := rl_coe _

lemma abs_cL (ξ'' : ZMod p → ZMod p) (x y m : ZMod p) :
    |cL ξ'' x y m| = cn (mu2 ξ'' x y * m) := abs_rl _

section cocycle

variable {T : Finset (ZMod p)} {B R : ℝ} {ξ'' : ZMod p → ZMod p}
  (hlin : ∀ x y, snorm T x ≤ R → snorm T y ≤ R → Good T B (mu2 ξ'' x y))
include hlin

lemma abs_cL_le {x y : ZMod p} (hx : snorm T x ≤ R) (hy : snorm T y ≤ R) (m : ZMod p) :
    |cL ξ'' x y m| ≤ B * snorm T m := by
  rw [abs_cL]; exact hlin x y hx hy m

lemma cL_cocycle {x y z m : ZMod p} (hx : snorm T x ≤ R) (hy : snorm T y ≤ R)
    (hz : snorm T z ≤ R) (hxy : snorm T (x + y) ≤ R) (hyz : snorm T (y + z) ≤ R)
    (hm : 4 * B * snorm T m < 1) :
    cL ξ'' x y m + cL ξ'' (x + y) z m = cL ξ'' x (y + z) m + cL ξ'' y z m := by
  have e : ((cL ξ'' x y m + cL ξ'' (x + y) z m - cL ξ'' x (y + z) m - cL ξ'' y z m : ℝ) :
      UnitAddCircle) = 0 := by
    simp only [AddCircle.coe_sub, AddCircle.coe_add, coe_cL, ← map_add, ← map_sub]
    rw [← map_zero (ZMod.toAddCircle (N := p))]
    congr 1
    simp only [mu2]
    rw [← add_assoc]
    ring
  have b1 := abs_cL_le hlin hx hy m
  have b2 := abs_cL_le hlin hxy hz m
  have b3 := abs_cL_le hlin hx hyz m
  have b4 := abs_cL_le hlin hy hz m
  have hb : |cL ξ'' x y m + cL ξ'' (x + y) z m - cL ξ'' x (y + z) m - cL ξ'' y z m| < 1 := by
    have t := abs_sub (cL ξ'' x y m + cL ξ'' (x + y) z m - cL ξ'' x (y + z) m) (cL ξ'' y z m)
    have t2 := abs_sub (cL ξ'' x y m + cL ξ'' (x + y) z m) (cL ξ'' x (y + z) m)
    have t3 := abs_add_le (cL ξ'' x y m) (cL ξ'' (x + y) z m)
    linarith
  linarith [eq_zero_of_coe_eq_zero e hb]

lemma cL_add_right (hB : 0 ≤ B) {x y : ZMod p} (hx : snorm T x ≤ R) (hy : snorm T y ≤ R)
    {m m' : ZMod p} (hm : 2 * B * (snorm T m + snorm T m') < 1) :
    cL ξ'' x y (m + m') = cL ξ'' x y m + cL ξ'' x y m' := by
  refine lift_add ?_ ?_
  · rw [coe_cL, coe_cL, coe_cL, mul_add, map_add]
  · have b1 := abs_cL_le hlin hx hy m
    have b2 := abs_cL_le hlin hx hy m'
    have b3 := abs_cL_le hlin hx hy (m + m')
    have := mul_le_mul_of_nonneg_left (snorm_add_le (S := T) m m') hB
    linarith

end cocycle

/-! ### The averaged correction -/

/-- `F₁(x)(m) = E_z c(x,z)(m)`. -/
def avgF1 (T : Finset (ZMod p)) (r3 : ℝ) (ξ'' : ZMod p → ZMod p) (x m : ZMod p) : ℝ :=
  ∑ z, regP T r3 z * cL ξ'' x z m

/-- `G_m(x) = ξ''(x) m / p + F₁(x)(m)`. -/
def G7 (T : Finset (ZMod p)) (r3 : ℝ) (ξ'' : ZMod p → ZMod p) (x m : ZMod p) : UnitAddCircle :=
  ZMod.toAddCircle (ξ'' x * m) + ((avgF1 T r3 ξ'' x m : ℝ) : UnitAddCircle)

/-- Translation of a regular average when the bound on the function only holds on a Bohr set
containing the relevant supports. -/
lemma shift_real_supp {T : Finset (ZMod p)} {ρ ρ' : ℝ} (hρ : 0 < ρ) (h4 : 4 * ρ' ≤ ρ)
    {y : ZMod p} (hy : snorm T y ≤ ρ') {Bg : ℝ} (g : ZMod p → ℝ)
    (hg : ∀ z, snorm T z ≤ ρ + ρ' → |g z| ≤ Bg) (hBg : 0 ≤ Bg) :
    |∑ z, regP T ρ z * g (z + y) - ∑ z, regP T ρ z * g z| ≤ Bg * (50 * T.card * ρ' / ρ) := by
  have hρ' : 0 ≤ ρ' := (snorm_nonneg y).trans hy
  set g' : ZMod p → ℝ := fun z => if snorm T z ≤ ρ + ρ' then g z else 0 with hg'
  have hb : ∀ z, |g' z| ≤ Bg := fun z => by
    simp only [hg']; split_ifs with h
    · exact hg z h
    · simpa using hBg
  have H := shift_real subset_rfl hρ h4 hy g' hb
  have e1 : ∀ z, regP T ρ z * g' (z + y) = regP T ρ z * g (z + y) := fun z => by
    by_cases hz : regP T ρ z = 0
    · simp [hz]
    · have hz' := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ.le hz) hρ.le
      have : snorm T (z + y) ≤ ρ + ρ' := (snorm_add_le z y).trans (add_le_add hz' hy)
      simp only [hg', if_pos this]
  have e2 : ∀ z, regP T ρ z * g' z = regP T ρ z * g z := fun z => by
    by_cases hz : regP T ρ z = 0
    · simp [hz]
    · have hz' := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ.le hz) hρ.le
      simp only [hg', if_pos (show snorm T z ≤ ρ + ρ' by linarith)]
  simp only [e1, e2] at H
  exact H

section avgF1

variable {T : Finset (ZMod p)} {B R r3 : ℝ} {ξ'' : ZMod p → ZMod p}
  (hlin : ∀ x y, snorm T x ≤ R → snorm T y ≤ R → Good T B (mu2 ξ'' x y))
  (hr3 : 0 < r3) (hr3R : r3 ≤ R)
include hlin hr3 hr3R

lemma snorm_le_of_regP {z : ZMod p} (hz : regP T r3 z ≠ 0) : snorm T z ≤ r3 :=
  snorm_le_of_mem (mem_bohr_of_regP_ne_zero hr3.le hz) hr3.le

lemma abs_F1_le {x : ZMod p} (hx : snorm T x ≤ R) (m : ZMod p) :
    |avgF1 T r3 ξ'' x m| ≤ B * snorm T m := by
  have hP := regP_isDist T hr3.le
  unfold avgF1
  refine abs_wavg_le hP.1 hP.2 _ fun z hz => ?_
  exact abs_cL_le hlin hx ((snorm_le_of_regP hlin hr3 hr3R hz).trans hr3R) m

lemma F1_add_right (hB : 0 ≤ B) {x : ZMod p} (hx : snorm T x ≤ R) {m m' : ZMod p}
    (hm : 2 * B * (snorm T m + snorm T m') < 1) :
    avgF1 T r3 ξ'' x (m + m') = avgF1 T r3 ξ'' x m + avgF1 T r3 ξ'' x m' := by
  unfold avgF1
  rw [← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  by_cases hz : regP T r3 z = 0
  · simp [hz]
  · rw [cL_add_right hlin hB hx ((snorm_le_of_regP hlin hr3 hr3R hz).trans hr3R) hm]; ring

lemma G7_add_right (hB : 0 ≤ B) {x : ZMod p} (hx : snorm T x ≤ R) {m m' : ZMod p}
    (hm : 2 * B * (snorm T m + snorm T m') < 1) :
    G7 T r3 ξ'' x (m + m') = G7 T r3 ξ'' x m + G7 T r3 ξ'' x m' := by
  unfold G7
  rw [F1_add_right hlin hr3 hr3R hB hx hm, mul_add, map_add, AddCircle.coe_add]
  abel

/-- The defect of `G_m`: it is proportional to the norm of the increment. -/
lemma G7_defect {x y m : ZMod p} {ρy : ℝ} (hxy : snorm T x + snorm T y ≤ R)
    (hy : snorm T y ≤ ρy) (hρy : r3 + ρy ≤ R) (h4 : 4 * ρy ≤ r3)
    (hm : 4 * B * snorm T m < 1) (hB : 0 ≤ B) :
    ‖G7 T r3 ξ'' (x + y) m - G7 T r3 ξ'' x m - G7 T r3 ξ'' y m‖ ≤
      B * snorm T m * (50 * T.card * ρy / r3) := by
  have hP := regP_isDist T hr3.le
  have hx : snorm T x ≤ R := by linarith [snorm_nonneg (S := T) y]
  have hyR : snorm T y ≤ R := by linarith [snorm_nonneg (S := T) x]
  have hxyR : snorm T (x + y) ≤ R := (snorm_add_le x y).trans hxy
  -- the exact identity
  have key : cL ξ'' x y m + (avgF1 T r3 ξ'' (x + y) m - avgF1 T r3 ξ'' x m - avgF1 T r3 ξ'' y m) =
      ∑ z, regP T r3 z * cL ξ'' x (z + y) m - ∑ z, regP T r3 z * cL ξ'' x z m := by
    have hc : ∀ z, regP T r3 z * cL ξ'' (x + y) z m - regP T r3 z * cL ξ'' y z m =
        regP T r3 z * cL ξ'' x (z + y) m - regP T r3 z * cL ξ'' x y m := fun z => by
      by_cases hz : regP T r3 z = 0
      · simp [hz]
      · have hzr := snorm_le_of_regP hlin hr3 hr3R hz
        have hyz : snorm T (y + z) ≤ R :=
          (snorm_add_le y z).trans (by linarith)
        have := cL_cocycle hlin hx hyR (hzr.trans hr3R) hxyR hyz hm
        rw [add_comm z y]
        linear_combination regP T r3 z * this
    have e : avgF1 T r3 ξ'' (x + y) m - avgF1 T r3 ξ'' x m - avgF1 T r3 ξ'' y m =
        ∑ z, regP T r3 z * cL ξ'' x (z + y) m - cL ξ'' x y m -
          ∑ z, regP T r3 z * cL ξ'' x z m := by
      unfold avgF1
      have : ∑ z, regP T r3 z * cL ξ'' (x + y) z m - ∑ z, regP T r3 z * cL ξ'' y z m =
          ∑ z, regP T r3 z * cL ξ'' x (z + y) m - ∑ z, regP T r3 z * cL ξ'' x y m := by
        rw [← sum_sub_distrib, ← sum_sub_distrib]
        exact sum_congr rfl fun z _ => hc z
      rw [← sum_mul, hP.2, one_mul] at this
      linarith
    rw [e]; ring
  have hbound : |∑ z, regP T r3 z * cL ξ'' x (z + y) m - ∑ z, regP T r3 z * cL ξ'' x z m| ≤
      B * snorm T m * (50 * T.card * ρy / r3) := by
    refine shift_real_supp hr3 h4 hy (fun z => cL ξ'' x z m) (fun z hz => ?_)
      (mul_nonneg hB (snorm_nonneg m))
    exact abs_cL_le hlin hx (hz.trans hρy) m
  have e2 : G7 T r3 ξ'' (x + y) m - G7 T r3 ξ'' x m - G7 T r3 ξ'' y m =
      ((cL ξ'' x y m + (avgF1 T r3 ξ'' (x + y) m - avgF1 T r3 ξ'' x m - avgF1 T r3 ξ'' y m) : ℝ) :
        UnitAddCircle) := by
    simp only [G7, AddCircle.coe_sub, AddCircle.coe_add, coe_cL, mu2, sub_mul, map_sub]
    abel
  rw [e2, key]
  exact (norm_coe_le_abs _).trans hbound

end avgF1

/-! ### Telescoping along coordinates -/

section tele

variable {T : Finset (ZMod p)} {G : ZMod p → UnitAddCircle} {R1 R2 D : ℝ}
  (hdef : ∀ x y, snorm T x ≤ R1 → snorm T y ≤ R2 → ‖G (x + y) - G x - G y‖ ≤ D * snorm T y)
include hdef

lemma tele_nat (k : ℕ) {x a : ZMod p} (hk : snorm T x + k * snorm T a ≤ R1)
    (ha : snorm T a ≤ R2) :
    ‖G (x + (k : ZMod p) * a) - G x - k • G a‖ ≤ k * (D * snorm T a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := snorm_nonneg (S := T) a
    have ih' := ih (by push_cast at hk; linarith)
    have hxk : snorm T (x + (k : ZMod p) * a) ≤ R1 := by
      refine (snorm_add_le _ _).trans ?_
      have := snorm_nsmul_le (S := T) k a
      push_cast at hk; linarith
    have d := hdef _ _ hxk ha
    have e : G (x + ((k + 1 : ℕ) : ZMod p) * a) - G x - (k + 1) • G a =
        (G (x + (k : ZMod p) * a + a) - G (x + (k : ZMod p) * a) - G a) +
          (G (x + (k : ZMod p) * a) - G x - k • G a) := by
      push_cast
      rw [show x + ((k : ZMod p) + 1) * a = x + (k : ZMod p) * a + a by ring, succ_nsmul]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    push_cast
    linarith

lemma tele_int (k : ℤ) {x a : ZMod p} (hk : snorm T x + 2 * |(k : ℝ)| * snorm T a ≤ R1)
    (ha : snorm T a ≤ R2) :
    ‖G (x + (k : ZMod p) * a) - G x - k • G a‖ ≤ |(k : ℝ)| * (D * snorm T a) := by
  have hs := snorm_nonneg (S := T) a
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [Int.cast_natCast, Nat.abs_cast, natCast_zsmul] at hk ⊢
    exact tele_nat hdef n (by nlinarith [abs_nonneg (n : ℝ)]) ha
  · simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, neg_smul,
      natCast_zsmul] at hk ⊢
    set x' := x + -((n : ZMod p) * a) with hx'
    have hsx' : snorm T x' ≤ snorm T x + n * snorm T a := by
      rw [hx', ← sub_eq_add_neg]
      exact (snorm_sub_le _ _).trans (add_le_add le_rfl (snorm_nsmul_le n a))
    have := tele_nat hdef n (x := x') (a := a) (by linarith) ha
    have e : x' + (n : ZMod p) * a = x := by rw [hx']; ring
    rw [e] at this
    have e2 : G (x + -(n : ZMod p) * a) - G x - -(n • G a) = -(G x - G x' - n • G a) := by
      rw [hx', neg_mul]; abel
    rw [e2, norm_neg]
    exact this

lemma tele_sum {ι : Type*} (s : Finset ι) (c : ι → ℤ) (a : ι → ZMod p)
    (hs : 2 * ∑ i ∈ s, |(c i : ℝ)| * snorm T (a i) ≤ R1)
    (ha : ∀ i ∈ s, c i ≠ 0 → snorm T (a i) ≤ R2) (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) :
    ‖G (∑ i ∈ s, (c i : ZMod p) * a i) - ∑ i ∈ s, c i • G (a i)‖ ≤
      D * ∑ i ∈ s, |(c i : ℝ)| * snorm T (a i) := by
  classical
  have hG0 : G 0 = 0 := by
    have := hdef 0 0 (by simpa using hR1) (by simpa using hR2)
    simp only [add_zero, snorm_zero, mul_zero, sub_self, zero_sub, norm_neg] at this
    exact norm_le_zero_iff.1 this
  induction s using Finset.induction_on with
  | empty => simp [hG0]
  | insert j s hj ih =>
    rw [sum_insert hj] at hs
    have hnn : 0 ≤ ∑ i ∈ s, |(c i : ℝ)| * snorm T (a i) :=
      sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (snorm_nonneg _)
    have hj0 : 0 ≤ |(c j : ℝ)| * snorm T (a j) := mul_nonneg (abs_nonneg _) (snorm_nonneg _)
    have ih' := ih (by linarith) (fun i hi => ha i (mem_insert_of_mem hi))
    rw [sum_insert hj, sum_insert hj, sum_insert hj]
    set X := ∑ i ∈ s, (c i : ZMod p) * a i
    have e : G ((c j : ZMod p) * a j + X) - (c j • G (a j) + ∑ i ∈ s, c i • G (a i)) =
        (G (X + (c j : ZMod p) * a j) - G X - c j • G (a j)) +
          (G X - ∑ i ∈ s, c i • G (a i)) := by
      rw [add_comm ((c j : ZMod p) * a j) X]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    by_cases hcj : c j = 0
    · simp only [hcj, Int.cast_zero, zero_mul, add_zero, zero_smul, sub_self,
        norm_zero, zero_add, abs_zero]
      exact ih'
    · have hX := snorm_sum_le (S := T) s c a
      have t := tele_int hdef (c j) (x := X) (a := a j) (by linarith)
        (ha j (mem_insert_self _ _) hcj)
      rw [mul_add]
      have : |(c j : ℝ)| * (D * snorm T (a j)) = D * (|(c j : ℝ)| * snorm T (a j)) := by ring
      linarith

end tele

/-! ### The bilinear form -/

/-- **Seventh step, algebraic part.**  From a `100%` approximately linear `ξ''` we build an
exactly bilinear `Ξ` close to `ξ''(n) m / p`. -/
theorem bilin7 (hp : p.Prime) {T : Finset (ZMod p)} (hT : ∃ s ∈ T, s ≠ 0) {B R r3 ρA : ℝ}
    (hB : 0 ≤ B) (hr3 : 0 < r3) (hρA : 0 < ρA)
    (h1 : 4 * (2 ^ (T.card ^ 2) * T.card) * ρA ≤ r3)
    (h2 : (2 * T.card + 1) * (2 ^ (T.card ^ 2) * T.card) * ρA + r3 ≤ R)
    (h3 : 2 * T.card * (2 ^ (T.card ^ 2) * T.card) * ρA < 1)
    (h4 : 4 * B * ρA < 1) (ξ'' : ZMod p → ZMod p)
    (hlin : ∀ x y, snorm T x ≤ R → snorm T y ≤ R → Good T B (ξ'' (x + y) - ξ'' x - ξ'' y)) :
    ∃ Ξ : ZMod p → ZMod p → UnitAddCircle,
      (∀ m, AddOn T ρA (fun n => Ξ n m)) ∧
      (∀ n, snorm T n ≤ ρA → AddOn T ρA (fun m => Ξ n m)) ∧
      ∀ n m, snorm T n ≤ ρA → snorm T m ≤ ρA →
        ‖Ξ n m - ZMod.toAddCircle (ξ'' n * m)‖ ≤
          B * snorm T m * (50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * snorm T n / r3
            + 1) := by
  have hlin' : ∀ x y, snorm T x ≤ R → snorm T y ≤ R → Good T B (mu2 ξ'' x y) := hlin
  set d := T.card with hd
  set Cb : ℝ := 2 ^ (d ^ 2) * d with hCb
  have hd1 : (1 : ℝ) ≤ d := by
    obtain ⟨s, hs, -⟩ := hT
    exact_mod_cast Finset.card_pos.2 ⟨s, hs⟩
  have hCb1 : 1 ≤ Cb := by
    have : (1 : ℝ) ≤ 2 ^ (d ^ 2) := one_le_pow₀ (by norm_num)
    nlinarith
  have hr3R : r3 ≤ R := by
    have : 0 ≤ (2 * (d : ℝ) + 1) * Cb * ρA := by positivity
    linarith
  obtain ⟨a, ℓ, hℓ, hsa, hrep, huniq⟩ := bohr_basis hp hT
  choose xc hxc using hrep
  have hxc' : ∀ x i, |(xc x i : ℝ)| * ℓ i ≤ Cb * snorm T x := fun x i => by
    rw [hCb, mul_assoc]; exact (hxc x).2 i
  -- coordinates are additive
  have hxadd : ∀ x y, snorm T x + snorm T y ≤ ρA → xc (x + y) = xc x + xc y := by
    intro x y hxy
    set k : Fin d → ℤ := xc (x + y) - xc x - xc y with hk
    have hk0 : ∑ i, (k i : ZMod p) * a i = 0 := by
      simp only [hk, Pi.sub_apply, Int.cast_sub, sub_mul, sum_sub_distrib]
      rw [← (hxc (x + y)).1, ← (hxc x).1, ← (hxc y).1]; ring
    have hkb : ∑ i, |(k i : ℝ)| * ℓ i < 1 := by
      have hpt : ∀ i, |(k i : ℝ)| * ℓ i ≤ Cb * (2 * ρA) := fun i => by
        have e1 := hxc' (x + y) i
        have e2 := hxc' x i
        have e3 := hxc' y i
        have hs := (snorm_add_le (S := T) x y)
        have : |(k i : ℝ)| ≤ |(xc (x + y) i : ℝ)| + |(xc x i : ℝ)| + |(xc y i : ℝ)| := by
          simp only [hk, Pi.sub_apply, Int.cast_sub]
          have := abs_sub ((xc (x + y) i : ℝ) - xc x i) (xc y i)
          have := abs_sub ((xc (x + y) i : ℝ)) (xc x i)
          linarith
        have hl := (hℓ i).le
        have hx0 := snorm_nonneg (S := T) x
        have hy0 := snorm_nonneg (S := T) y
        calc |(k i : ℝ)| * ℓ i ≤ (|(xc (x + y) i : ℝ)| + |(xc x i : ℝ)| + |(xc y i : ℝ)|) * ℓ i :=
              mul_le_mul_of_nonneg_right this hl
          _ ≤ Cb * snorm T (x + y) + Cb * snorm T x + Cb * snorm T y := by
              rw [add_mul, add_mul]; exact add_le_add (add_le_add e1 e2) e3
          _ ≤ Cb * (2 * ρA) := by
              have hCb0 : 0 ≤ Cb := by linarith
              have : snorm T (x + y) + snorm T x + snorm T y ≤ 2 * ρA := by linarith
              nlinarith [mul_le_mul_of_nonneg_left this hCb0]
      calc ∑ i, |(k i : ℝ)| * ℓ i ≤ ∑ _i : Fin d, Cb * (2 * ρA) := sum_le_sum fun i _ => hpt i
        _ = d * (Cb * (2 * ρA)) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < 1 := by nlinarith
    have := huniq k hk0 hkb
    funext i
    have := congrFun this i
    simp only [hk, Pi.sub_apply, Pi.zero_apply] at this
    simp only [Pi.add_apply]; omega
  -- basis vectors used by small elements are small
  have hsmall : ∀ n i, xc n i ≠ 0 → snorm T (a i) ≤ Cb * snorm T n := by
    intro n i hi
    have h1' : (1 : ℝ) ≤ |(xc n i : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
    calc snorm T (a i) ≤ ℓ i := hsa i
      _ ≤ |(xc n i : ℝ)| * ℓ i := by nlinarith [hℓ i]
      _ ≤ Cb * snorm T n := hxc' n i
  have hCb0 : 0 ≤ Cb := by linarith
  have hd0 : (0 : ℝ) ≤ d := by linarith
  refine ⟨fun n m => ∑ i, xc n i • G7 T r3 ξ'' (a i) m, ?_, ?_, ?_⟩
  · intro m x y hxy
    try simp only
    rw [hxadd x y hxy, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by rw [Pi.add_apply, add_zsmul]
  · intro n hn x y hxy
    try simp only
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : xc n i = 0
    · simp [hi]
    · have hai : snorm T (a i) ≤ R := by
        have := hsmall n i hi
        have : Cb * snorm T n ≤ Cb * ρA := mul_le_mul_of_nonneg_left hn hCb0
        nlinarith
      have hm : 2 * B * (snorm T x + snorm T y) < 1 := by
        have := mul_le_mul_of_nonneg_left hxy (show 0 ≤ 2 * B by linarith)
        linarith
      rw [G7_add_right hlin' hr3 hr3R hB hai hm, zsmul_add]
  · intro n m hn hm
    have hm0 := snorm_nonneg (S := T) m
    have hn0 := snorm_nonneg (S := T) n
    set D := B * snorm T m * (50 * d / r3) with hD
    have hD0 : 0 ≤ D := mul_nonneg (mul_nonneg hB hm0) (div_nonneg (by linarith) hr3.le)
    have hdef : ∀ x y, snorm T x ≤ 2 * d * Cb * ρA → snorm T y ≤ Cb * ρA →
        ‖G7 T r3 ξ'' (x + y) m - G7 T r3 ξ'' x m - G7 T r3 ξ'' y m‖ ≤ D * snorm T y := by
      intro x y hx hy
      have h4B : 4 * B * snorm T m < 1 := by
        have := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 * B by linarith); linarith
      have := G7_defect hlin' hr3 hr3R (x := x) (y := y) (m := m) (ρy := snorm T y)
        (by nlinarith) le_rfl (by nlinarith) (by nlinarith) h4B hB
      calc _ ≤ _ := this
        _ = D * snorm T y := by rw [hD]; ring
    have hsumb : ∑ i, |(xc n i : ℝ)| * snorm T (a i) ≤ d * (Cb * snorm T n) := by
      calc ∑ i, |(xc n i : ℝ)| * snorm T (a i) ≤ ∑ _i : Fin d, Cb * snorm T n :=
            sum_le_sum fun i _ => (mul_le_mul_of_nonneg_left (hsa i) (abs_nonneg _)).trans
              (hxc' n i)
        _ = d * (Cb * snorm T n) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have tele := tele_sum hdef (s := univ) (xc n) a
      (by
        have : d * (Cb * snorm T n) ≤ d * (Cb * ρA) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hCb0) hd0
        nlinarith)
      (fun i _ hi => (hsmall n i hi).trans (mul_le_mul_of_nonneg_left hn hCb0))
      (by have := mul_nonneg hCb0 hρA.le; nlinarith) (mul_nonneg hCb0 hρA.le)
    rw [← (hxc n).1] at tele
    have hF := abs_F1_le hlin' hr3 hr3R (x := n) (by nlinarith) m
    have e : (∑ i, xc n i • G7 T r3 ξ'' (a i) m) - ZMod.toAddCircle (ξ'' n * m) =
        -(G7 T r3 ξ'' n m - ∑ i, xc n i • G7 T r3 ξ'' (a i) m) +
          ((avgF1 T r3 ξ'' n m : ℝ) : UnitAddCircle) := by
      simp only [G7]; abel
    try simp only
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    have hc := norm_coe_le_abs (avgF1 T r3 ξ'' n m)
    have ht2 : D * ∑ i, |(xc n i : ℝ)| * snorm T (a i) ≤ D * (d * (Cb * snorm T n)) :=
      mul_le_mul_of_nonneg_left hsumb hD0
    calc _ ≤ D * (d * (Cb * snorm T n)) + B * snorm T m := by linarith
      _ = _ := by rw [hD]; field_simp

end

end GT
end File_GT_U3S8a

open Finset KM
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {T : Finset (ZMod p)} (hT : ∃ s ∈ T, s ≠ 0) {B R r3 ρA : ℝ}
    (hB : 0 ≤ B) (hr3 : 0 < r3) (hρA : 0 < ρA)
    (h1 : 4 * (2 ^ (T.card ^ 2) * T.card) * ρA ≤ r3)
    (h2 : (2 * T.card + 1) * (2 ^ (T.card ^ 2) * T.card) * ρA + r3 ≤ R)
    (h3 : 2 * T.card * (2 ^ (T.card ^ 2) * T.card) * ρA < 1)
    (h4 : 4 * B * ρA < 1) (ξ'' : ZMod p → ZMod p)
    (hlin : ∀ x y, snorm T x ≤ R → snorm T y ≤ R → Good T B (ξ'' (x + y) - ξ'' x - ξ'' y)) :
    ∃ Ξ : ZMod p → ZMod p → UnitAddCircle,
      (∀ m, AddOn T ρA (fun n => Ξ n m)) ∧
      (∀ n, snorm T n ≤ ρA → AddOn T ρA (fun m => Ξ n m)) ∧
      ∀ n m, snorm T n ≤ ρA → snorm T m ≤ ρA →
        ‖Ξ n m - ZMod.toAddCircle (ξ'' n * m)‖ ≤
          B * snorm T m * (50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * snorm T n / r3
            + 1) :=
  @GT.bilin7 p _ hp T hT B R r3 ρA hB hr3 hρA h1 h2 h3 h4 ξ'' hlin

