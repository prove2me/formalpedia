-- Prove2me | solution 1 for GT.u3_back
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:50.026481+00:00
-- url     : https://prove2.me/submissions/62eaa186-735d-4268-aa45-279ef5cc5b55

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_bilin7
import Theorems.Thm_GT_large_quad

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

lemma ec_sub (x y : UnitAddCircle) : ec (x - y) = ec x * conj (ec y) := by
  rw [sub_eq_add_neg, ec_add, ec_neg]

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

lemma mono (h : AddOn S R f) {R' : ℝ} (hR : R' ≤ R) : AddOn S R' f :=
  fun x y hxy => h x y (hxy.trans hR)

lemma map_zero (h : AddOn S R f) (hR : 0 ≤ R) : f 0 = 0 := by
  have := h 0 0 (by simp [hR])
  rw [add_zero] at this
  exact add_left_cancel (a := f 0) (by rw [add_zero]; exact this.symm)

lemma map_nsmul (h : AddOn S R f) (n : ℕ) (x : ZMod p) (hn : n * snorm S x ≤ R) :
    f ((n : ZMod p) * x) = n • f x := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, zero_smul]; exact h.map_zero (by simpa using hn)
  | succ n ih =>
    have hs := snorm_nonneg (S := S) x
    have e : ((n + 1 : ℕ) : ZMod p) * x = (n : ZMod p) * x + x := by push_cast; ring
    rw [e, h _ _ ?_, ih ?_, succ_nsmul]
    · push_cast at hn; nlinarith
    · refine le_trans (add_le_add (snorm_nsmul_le n x) le_rfl) ?_
      push_cast at hn; linarith

lemma map_neg (h : AddOn S R f) (x : ZMod p) (hx : 2 * snorm S x ≤ R) : f (-x) = -f x := by
  have hR : 0 ≤ R := le_trans (by have := snorm_nonneg (S := S) x; linarith) hx
  have := h x (-x) (by rw [snorm_neg]; linarith)
  rw [add_neg_cancel, h.map_zero hR] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

lemma neg (h : AddOn S R f) : AddOn S R (fun x => -f x) := fun x y hxy => by
  simp only; rw [h x y hxy, neg_add]

lemma add {g : ZMod p → M} (hf : AddOn S R f) (hg : AddOn S R g) :
    AddOn S R (fun x => f x + g x) := fun x y hxy => by
  simp only; rw [hf x y hxy, hg x y hxy]; abel

lemma sub {g : ZMod p → M} (hf : AddOn S R f) (hg : AddOn S R g) :
    AddOn S R (fun x => f x - g x) := fun x y hxy => by
  simp only; rw [hf x y hxy, hg x y hxy]; abel

end AddOn

end

end GT
end File_GT_AddOn

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

end

end GT
end File_GT_LocQ

section File_GT_CS
/-!
# The double Cauchy–Schwarz inequality used in Weyl differencing
-/

open Finset
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

lemma conj_ec (x : UnitAddCircle) : conj (ec x) = ec (-x) := (ec_neg x).symm

lemma ofReal_norm_sq_wsum (c : α → ℝ) (u : α → ℂ) :
    ((‖∑ i, (c i : ℂ) * u i‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * (u i * conj (u j)) := by
  rw [ofReal_norm_sq, map_sum, sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [map_mul, Complex.conj_ofReal]; push_cast; ring

/-- **Double Cauchy–Schwarz.** -/
theorem cs2 {P : α → ℝ} {Q : β → ℝ} (hP : ∀ r, 0 ≤ P r) (hP1 : ∑ r, P r = 1)
    (hQ : ∀ h, 0 ≤ Q h) (hQ1 : ∑ h, Q h = 1) (b1 : α → ℂ) (b2 : β → ℂ)
    (hb1 : ∀ r, ‖b1 r‖ ≤ 1) (hb2 : ∀ h, ‖b2 h‖ ≤ 1) (X : α → β → UnitAddCircle) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h : δ ≤ ‖∑ r, ∑ h, (P r : ℂ) * (Q h : ℂ) * (b1 r * b2 h * ec (X r h))‖) :
    δ ^ 4 ≤ ‖∑ r, ∑ r', ∑ h, ∑ h', ((P r * P r' * Q h * Q h' : ℝ) : ℂ) *
      ec (X r h - X r h' - X r' h + X r' h')‖ := by
  obtain ⟨T, hT⟩ : ∃ T : α → ℂ, ∀ r, T r = ∑ h, (Q h : ℂ) * (b2 h * ec (X r h)) :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∑ r, ∑ h, (P r : ℂ) * (Q h : ℂ) * (b1 r * b2 h * ec (X r h)) =
      ∑ r, (P r : ℂ) * (b1 r * T r) := by
    refine sum_congr rfl fun r _ => ?_
    rw [hT, mul_sum, mul_sum]; exact sum_congr rfl fun h _ => by ring
  have h1 : δ ≤ ∑ r, P r * ‖T r‖ := by
    refine h.trans ?_
    rw [e0]
    refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP r)]
    refine mul_le_mul_of_nonneg_left ?_ (hP r)
    calc ‖b1 r‖ * ‖T r‖ ≤ 1 * ‖T r‖ := mul_le_mul_of_nonneg_right (hb1 r) (norm_nonneg _)
      _ = ‖T r‖ := one_mul _
  have h2 : δ ^ 2 ≤ ∑ r, P r * ‖T r‖ ^ 2 :=
    le_trans (pow_le_pow_left₀ hδ h1 2) (sq_wavg_le _ hP hP1)
  obtain ⟨U, hU⟩ : ∃ U : β → β → ℂ, ∀ h h', U h h' = ∑ r, (P r : ℂ) * ec (X r h - X r h') :=
    ⟨_, fun _ _ => rfl⟩
  have h3 : ((∑ r, P r * ‖T r‖ ^ 2 : ℝ) : ℂ) =
      ∑ h, ∑ h', ((Q h * Q h' : ℝ) : ℂ) * (b2 h * conj (b2 h') * U h h') := by
    push_cast
    have : ∀ r, (P r : ℂ) * ((‖T r‖ ^ 2 : ℝ) : ℂ) = ∑ h, ∑ h', (P r : ℂ) *
        (((Q h * Q h' : ℝ) : ℂ) * (b2 h * conj (b2 h') * ec (X r h - X r h'))) := by
      intro r
      rw [hT, ofReal_norm_sq_wsum, mul_sum]
      refine sum_congr rfl fun h _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun h' _ => ?_
      rw [map_mul, conj_ec, sub_eq_add_neg, ec_add]
      ring
    push_cast at this
    rw [sum_congr rfl fun r _ => this r, sum_comm]
    refine sum_congr rfl fun h _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun h' _ => ?_
    rw [hU, mul_sum, mul_sum]
    exact sum_congr rfl fun r _ => by ring
  have h4 : δ ^ 2 ≤ ∑ h, ∑ h', Q h * Q h' * ‖U h h'‖ := by
    refine h2.trans ?_
    have e := congrArg norm h3
    rw [Complex.norm_real, Real.norm_eq_abs] at e
    refine (le_abs_self _).trans (e ▸ ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun h _ => (norm_sum_le _ _).trans
      (sum_le_sum fun h' _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hQ h) (hQ h')), norm_mul, norm_mul, Complex.norm_conj]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hQ h) (hQ h'))
    have := mul_le_mul (hb2 h) (hb2 h') (norm_nonneg _) zero_le_one
    calc ‖b2 h‖ * ‖b2 h'‖ * ‖U h h'‖ ≤ 1 * 1 * ‖U h h'‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖U h h'‖ := by ring
  -- second application
  have hQQ : ∀ z : β × β, 0 ≤ Q z.1 * Q z.2 := fun z => mul_nonneg (hQ _) (hQ _)
  have hQQ1 : ∑ z : β × β, Q z.1 * Q z.2 = 1 := by
    simp only [Fintype.sum_prod_type, ← mul_sum, hQ1, mul_one]
  have h5 : δ ^ 4 ≤ ∑ h, ∑ h', Q h * Q h' * ‖U h h'‖ ^ 2 := by
    have := sq_wavg_le (fun z : β × β => ‖U z.1 z.2‖) hQQ hQQ1
    simp only [Fintype.sum_prod_type] at this
    calc δ ^ 4 = (δ ^ 2) ^ 2 := by ring
      _ ≤ (∑ h, ∑ h', Q h * Q h' * ‖U h h'‖) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      _ ≤ _ := this
  have h6 : ((∑ h, ∑ h', Q h * Q h' * ‖U h h'‖ ^ 2 : ℝ) : ℂ) =
      ∑ r, ∑ r', ∑ h, ∑ h', ((P r * P r' * Q h * Q h' : ℝ) : ℂ) *
        ec (X r h - X r h' - X r' h + X r' h') := by
    push_cast
    have : ∀ h h', (Q h : ℂ) * (Q h' : ℂ) * ((‖U h h'‖ ^ 2 : ℝ) : ℂ) = ∑ r, ∑ r',
        ((P r * P r' * Q h * Q h' : ℝ) : ℂ) * ec (X r h - X r h' - X r' h + X r' h') := by
      intro h h'
      rw [hU, ofReal_norm_sq_wsum, mul_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun r' _ => ?_
      rw [conj_ec, ← ec_add]
      push_cast
      rw [show X r h - X r h' + -(X r' h - X r' h') = X r h - X r h' - X r' h + X r' h' by abel]
      ring
    push_cast at this
    rw [sum_congr rfl fun h _ => sum_congr rfl fun h' _ => this h h']
    obtain ⟨G, hG⟩ : ∃ G : α → α → β → β → ℂ, ∀ r r' h h', G r r' h h' =
        (P r : ℂ) * (P r' : ℂ) * (Q h : ℂ) * (Q h' : ℂ) * ec (X r h - X r h' - X r' h + X r' h') :=
      ⟨_, fun _ _ _ _ => rfl⟩
    simp only [← hG]
    calc ∑ h, ∑ h', ∑ r, ∑ r', G r r' h h' = ∑ h, ∑ r, ∑ r', ∑ h', G r r' h h' :=
          sum_congr rfl fun h _ => by
            rw [sum_comm]; exact sum_congr rfl fun r _ => sum_comm
      _ = ∑ r, ∑ r', ∑ h, ∑ h', G r r' h h' := by
            rw [sum_comm]; refine sum_congr rfl fun r _ => ?_
            rw [sum_comm]
  rw [← h6, Complex.norm_real, Real.norm_eq_abs]
  exact h5.trans (le_abs_self _)

end

end GT
end File_GT_CS

section File_GT_LargeQuad
/-!
# Large local quadratic exponential sums (Green–Tao, Proposition 4.9)
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- Pigeonhole for a double average. -/
lemma exists_pair_ge {Γ : Finset (ZMod p)} {ρ1 ρ : ℝ} (hρ1 : 0 ≤ ρ1) (hρ : 0 ≤ ρ)
    (G : ZMod p → ZMod p → ℝ) {c : ℝ}
    (h : c ≤ ∑ x, ∑ y, regP Γ ρ1 x * regP Γ ρ y * G x y) :
    ∃ x y, regP Γ ρ1 x ≠ 0 ∧ regP Γ ρ y ≠ 0 ∧ c ≤ G x y := by
  have hD := regP_isDist Γ hρ
  have hD1 := regP_isDist Γ hρ1
  have hP : ∀ z : ZMod p × ZMod p, 0 ≤ regP Γ ρ1 z.1 * regP Γ ρ z.2 :=
    fun z => mul_nonneg (hD1.1 _) (hD.1 _)
  have hP1 : ∑ z : ZMod p × ZMod p, regP Γ ρ1 z.1 * regP Γ ρ z.2 = 1 := by
    simp only [Fintype.sum_prod_type, ← mul_sum, hD.2, mul_one, hD1.2]
  obtain ⟨z, hz, hcz⟩ := exists_pos_ge hP hP1 (fun z => G z.1 z.2) (c := c) (by
    rw [Fintype.sum_prod_type]; exact h)
  exact ⟨z.1, z.2, left_ne_zero_of_mul hz, right_ne_zero_of_mul hz, hcz⟩

end

end GT
end File_GT_LargeQuad

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

lemma sum_regP_neg (Γ : Finset (ZMod p)) (ρ : ℝ) (F : ZMod p → ℂ) :
    ∑ x, (regP Γ ρ x : ℂ) * F (-x) = ∑ x, (regP Γ ρ x : ℂ) * F x :=
  Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => by simp [regP_neg])

/-! ### Goodness -/

namespace Good

variable {T : Finset (ZMod p)} {A A' : ℝ} {l l' : ZMod p}

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

end

end GT
end File_GT_U3Base

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

end

end GT
end File_GT_U3S2

section File_GT_U3S8b
/-!
# Local inverse `U³`, eighth step: making the bilinear form symmetric

Green–Tao, Theorem 9.12.  If a derivative of `f` correlates with a locally bilinear phase
`Ξ(n₁, m₁)`, then some bounded multiple of the antisymmetric part
`{n, m} = Ξ(n, m) - Ξ(m, n)` is small on a small Bohr set.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

set_option maxHeartbeats 2000000 in
/-- The tail of the symmetry argument: a large correlation of a locally bilinear phase `X`
against bounded functions of each variable forces a bounded multiple of `X` to be small. -/
theorem bilin_tail (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0)
    {X : ZMod p → ZMod p → UnitAddCircle} {ρr ρh : ℝ} (hρh : 0 < ρh) (hhr : ρh ≤ ρr)
    (H1 : ∀ m, snorm S m ≤ 2 * ρr → AddOn S (2 * ρr) (fun n => X n m))
    (H2 : ∀ n, snorm S n ≤ 2 * ρr → AddOn S (2 * ρr) (fun m => X n m))
    (b1 b2 : ZMod p → ℂ) (hb1 : ∀ r, ‖b1 r‖ ≤ 1)
    (hb2 : ∀ h, ‖b2 h‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : δ ≤ ‖∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
      (b1 r * b2 h * ec (X r h))‖) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (32 / δ ^ 4) ^ (S.card ^ 2) ∧
      ∀ n m, snorm S n ≤ lqR S.card (δ ^ 4) ρh → snorm S m ≤ lqR S.card (δ ^ 4) ρh →
        ‖q • X n m‖ ≤ lqK S.card (δ ^ 4) ρh * snorm S n * snorm S m := by
  have hρr : 0 < ρr := lt_of_lt_of_le hρh hhr
  have hDr := regP_isDist S hρr.le
  have hDh := regP_isDist S hρh.le
  have hcs := cs2 hDr.1 hDr.2 hDh.1 hDh.2 b1 b2 hb1 hb2 X hδ.le h
  obtain ⟨W, hW⟩ : ∃ W : ZMod p → ZMod p → ℂ, ∀ r' h', W r' h' = ∑ r, ∑ h,
      (regP S ρr r : ℂ) * (regP S ρh h : ℂ) * ec (X r h - X r h' - X r' h + X r' h') :=
    ⟨_, fun _ _ => rfl⟩
  have hre : ∑ r, ∑ r', ∑ h, ∑ h', ((regP S ρr r * regP S ρr r' * regP S ρh h *
      regP S ρh h' : ℝ) : ℂ) * ec (X r h - X r h' - X r' h + X r' h') =
      ∑ r', ∑ h', (regP S ρr r' : ℂ) * (regP S ρh h' : ℂ) * W r' h' := by
    obtain ⟨G, hG⟩ : ∃ G : ZMod p → ZMod p → ZMod p → ZMod p → ℂ, ∀ r r' h h', G r r' h h' =
        (regP S ρr r' : ℂ) * (regP S ρh h' : ℂ) * ((regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
          ec (X r h - X r h' - X r' h + X r' h')) := ⟨_, fun _ _ _ _ => rfl⟩
    have e1 : ∀ r r' h h', ((regP S ρr r * regP S ρr r' * regP S ρh h *
        regP S ρh h' : ℝ) : ℂ) * ec (X r h - X r h' - X r' h + X r' h') = G r r' h h' := by
      intro r r' h h'; rw [hG]; push_cast; ring
    have rhs : ∑ r', ∑ h', (regP S ρr r' : ℂ) * (regP S ρh h' : ℂ) * W r' h' =
        ∑ r', ∑ h', ∑ r, ∑ h, G r r' h h' := by
      refine sum_congr rfl fun r' _ => sum_congr rfl fun h' _ => ?_
      rw [hW, mul_sum]; refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun h _ => ?_
      rw [hG]
    rw [rhs]
    simp only [e1]
    calc ∑ r, ∑ r', ∑ h, ∑ h', G r r' h h' = ∑ r', ∑ r, ∑ h, ∑ h', G r r' h h' := sum_comm
      _ = ∑ r', ∑ r, ∑ h', ∑ h, G r r' h h' :=
          sum_congr rfl fun r' _ => sum_congr rfl fun r _ => sum_comm
      _ = ∑ r', ∑ h', ∑ r, ∑ h, G r r' h h' := sum_congr rfl fun r' _ => sum_comm
  rw [hre] at hcs
  have hcs' : δ ^ 4 ≤ ∑ r', ∑ h', regP S ρr r' * regP S ρh h' * ‖W r' h'‖ := by
    refine hcs.trans ((norm_sum_le _ _).trans (sum_le_sum fun r' _ => (norm_sum_le _ _).trans
      (sum_le_sum fun h' _ => le_of_eq ?_)))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (regP_nonneg S r'), abs_of_nonneg (regP_nonneg S h')]
  obtain ⟨r', h', hr', hh', hW'⟩ := exists_pair_ge hρr.le hρh.le _ hcs'
  have hsr' : snorm S r' ≤ ρr := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρr.le hr') hρr.le
  have hsh' : snorm S h' ≤ ρh := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρh.le hh') hρh.le
  have hW2 : δ ^ 4 ≤ ‖∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
      ec (X r h + (fun r => -X r h') r + (fun h => -X r' h) h)‖ := by
    refine hW'.trans (le_of_eq ?_)
    rw [hW]
    have e : ∑ r, ∑ h, (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
        ec (X r h - X r h' - X r' h + X r' h') = ec (X r' h') * ∑ r, ∑ h,
        (regP S ρr r : ℂ) * (regP S ρh h : ℂ) *
          ec (X r h + (fun r => -X r h') r + (fun h => -X r' h) h) := by
      rw [mul_sum]; refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun h _ => ?_
      try simp only
      rw [show X r h - X r h' - X r' h + X r' h' = X r' h' + (X r h + -X r h' + -X r' h) by abel,
        ec_add]
      ring
    rw [e, norm_mul, norm_ec, one_mul]
  have H3 : AddOn S (2 * ρr) (fun r => -X r h') := (H1 h' (by linarith)).neg
  have H4 : AddOn S (2 * ρr) (fun h => -X r' h) := (H2 r' (by linarith)).neg
  obtain ⟨q, hq1, hq2, hq3⟩ := large_quad (φ := X) (lam := fun r => -X r h')
    (mu := fun h => -X r' h) hp hS hρh hhr (pow_pos hδ 4) (pow_le_one₀ hδ.le hδ1) H1 H2 H3 H4 hW2
  exact ⟨q, hq1, hq2, hq3⟩

lemma norm_sq_le_norm_of_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖z‖ ^ 2 ≤ ‖z‖ := by
  have := norm_nonneg z
  nlinarith

/-- **Eighth step** (Green–Tao, Theorem 9.12): the antisymmetric part of `Ξ` is essentially
torsion. -/
theorem sym8 (hp : p.Prime) {T : Finset (ZMod p)} (hT : ∃ s ∈ T, s ≠ 0)
    {ρA ρ5 ρ6 : ℝ} (hρ6 : 0 < ρ6) (h65 : 8 * ρ6 ≤ ρ5) (h5A : 4 * ρ5 ≤ ρA)
    {Ξ : ZMod p → ZMod p → UnitAddCircle}
    (hΞ1 : ∀ m, AddOn T ρA (fun n => Ξ n m))
    (hΞ2 : ∀ n, snorm T n ≤ ρA → AddOn T ρA (fun m => Ξ n m))
    (g2 g3 : ZMod p → ℂ) (hg2 : ∀ x, ‖g2 x‖ ≤ 1) (hg3 : ∀ x, ‖g3 x‖ ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ ∑ n1, regP T ρ6 n1 *
      ‖∑ m1, (regP T ρ5 m1 : ℂ) * (g2 (m1 - n1) * g3 m1 * ec (Ξ n1 m1))‖ ^ 2)
    (hδ : 0 < c ^ 2 - 100 * T.card * ρ6 / ρ5) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (32 / (c ^ 2 - 100 * T.card * ρ6 / ρ5) ^ 4) ^ (T.card ^ 2) ∧
      ∀ n m, snorm T n ≤ lqR T.card ((c ^ 2 - 100 * T.card * ρ6 / ρ5) ^ 4) ρ6 →
        snorm T m ≤ lqR T.card ((c ^ 2 - 100 * T.card * ρ6 / ρ5) ^ 4) ρ6 →
        ‖q • (Ξ n m - Ξ m n)‖ ≤
          lqK T.card ((c ^ 2 - 100 * T.card * ρ6 / ρ5) ^ 4) ρ6 * snorm T n * snorm T m := by
  have hρ5 : 0 < ρ5 := by linarith
  have hP5 := regP_isDist T hρ5.le
  have hP6 := regP_isDist T hρ6.le
  set δ := c ^ 2 - 100 * T.card * ρ6 / ρ5 with hδdef
  set A : ZMod p → ℂ := fun n1 =>
    ∑ m1, (regP T ρ5 m1 : ℂ) * (g2 (m1 - n1) * g3 m1 * ec (Ξ n1 m1)) with hA
  have hA1 : ∀ n1, ‖A n1‖ ≤ 1 := fun n1 => by
    refine norm_wavg_le hP5.1 hP5.2 _ fun m1 _ => ?_
    rw [norm_mul, norm_mul, norm_ec, mul_one]
    exact mul_le_one₀ (hg2 _) (norm_nonneg _) (hg3 _)
  -- Step 1: from `L²` to `L¹`
  have hc1 : c ≤ ∑ n1, regP T ρ6 n1 * ‖A n1‖ :=
    hc.trans (sum_le_sum fun n1 _ => mul_le_mul_of_nonneg_left
      (norm_sq_le_norm_of_le_one (hA1 n1)) (hP6.1 n1))
  choose u hu1 hu2 using fun n1 => exists_unit_mul (A n1)
  set W : ZMod p → ℂ := fun m1 =>
    ∑ n1, (regP T ρ6 n1 : ℂ) * (u n1 * g2 (m1 - n1) * ec (Ξ n1 m1)) with hW
  have hsw : ∑ n1, (regP T ρ6 n1 : ℂ) * (u n1 * A n1) =
      ∑ m1, (regP T ρ5 m1 : ℂ) * (g3 m1 * W m1) := by
    simp only [hA, hW, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun m1 _ => sum_congr rfl fun n1 _ => ?_
    ring
  have hc2 : c ≤ ‖∑ m1, (regP T ρ5 m1 : ℂ) * (g3 m1 * W m1)‖ := by
    rw [← hsw]
    have e : ∑ n1, (regP T ρ6 n1 : ℂ) * (u n1 * A n1) =
        ((∑ n1, regP T ρ6 n1 * ‖A n1‖ : ℝ) : ℂ) := by
      push_cast; exact sum_congr rfl fun n1 _ => by rw [hu2]
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact hc1.trans (le_abs_self _)
  -- Step 2: Cauchy–Schwarz eliminating `g₃`
  have hc3 : c ^ 2 ≤ ∑ m1, regP T ρ5 m1 * ‖W m1‖ ^ 2 := by
    have := norm_wsum_sq_le hP5.1 hP5.2 (fun m1 => g3 m1 * W m1)
    refine (pow_le_pow_left₀ hc0 hc2 2).trans (this.trans (sum_le_sum fun m1 _ => ?_))
    refine mul_le_mul_of_nonneg_left ?_ (hP5.1 m1)
    rw [norm_mul, mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (hg3 m1))
  -- expansion of `|W|²`
  set H : ZMod p → ZMod p → ZMod p → ℂ := fun n1 n1' m1 =>
    u n1 * conj (u n1') * (g2 (m1 - n1) * conj (g2 (m1 - n1'))) *
      ec (Ξ n1 m1 - Ξ n1' m1) with hH
  have hexp : ((∑ m1, regP T ρ5 m1 * ‖W m1‖ ^ 2 : ℝ) : ℂ) =
      ∑ n1, ∑ n1', ((regP T ρ6 n1 * regP T ρ6 n1' : ℝ) : ℂ) *
        ∑ m1, (regP T ρ5 m1 : ℂ) * H n1 n1' m1 := by
    push_cast
    have e1 : ∀ m1, ((‖W m1‖ ^ 2 : ℝ) : ℂ) = ∑ n1, ∑ n1',
        ((regP T ρ6 n1 * regP T ρ6 n1' : ℝ) : ℂ) * H n1 n1' m1 := fun m1 => by
      rw [hW, ofReal_norm_sq_wsum]
      refine sum_congr rfl fun n1 _ => sum_congr rfl fun n1' _ => ?_
      simp only [hH, map_mul, conj_ec, ec_sub]
      ring
    have e1' : ∀ m1, ((‖W m1‖ : ℂ)) ^ 2 = ∑ n1, ∑ n1',
        ((regP T ρ6 n1 * regP T ρ6 n1' : ℝ) : ℂ) * H n1 n1' m1 := fun m1 => by
      rw [← e1]; push_cast; ring
    simp only [e1', mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n1 _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun n1' _ => sum_congr rfl fun m1 _ => ?_
    push_cast; ring
  -- Step 3: the change of variables `k = n₁ + n₁' - m₁`
  set b3 : ZMod p → ZMod p → ℂ := fun n1 k =>
    u n1 * conj (g2 (n1 - k)) * ec (Ξ n1 n1 - Ξ n1 k) with hb3
  set b4 : ZMod p → ZMod p → ℂ := fun n1' k =>
    conj (u n1') * g2 (n1' - k) * ec (Ξ n1' k - Ξ n1' n1') with hb4
  have hb3b : ∀ n1 k, ‖b3 n1 k‖ ≤ 1 := fun n1 k => by
    simp only [hb3, norm_mul, norm_ec, mul_one, Complex.norm_conj]
    exact mul_le_one₀ (hu1 n1) (norm_nonneg _) (hg2 _)
  have hb4b : ∀ n1 k, ‖b4 n1 k‖ ≤ 1 := fun n1 k => by
    simp only [hb4, norm_mul, norm_ec, mul_one, Complex.norm_conj]
    exact mul_le_one₀ (hu1 n1) (norm_nonneg _) (hg2 _)
  set X : ZMod p → ZMod p → UnitAddCircle := fun n m => Ξ n m - Ξ m n with hX
  have hcv : ∀ n1 n1', regP T ρ6 n1 ≠ 0 → regP T ρ6 n1' ≠ 0 →
      ‖∑ m1, (regP T ρ5 m1 : ℂ) * H n1 n1' m1 -
        ∑ k, (regP T ρ5 k : ℂ) * (b3 n1 k * b4 n1' k * ec (X n1 n1'))‖ ≤
        100 * T.card * ρ6 / ρ5 := by
    intro n1 n1' h1 h1'
    have hs1 : snorm T n1 ≤ ρ6 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ6.le h1) hρ6.le
    have hs1' : snorm T n1' ≤ ρ6 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ6.le h1') hρ6.le
    set t := n1 + n1' with ht
    have hst : snorm T t ≤ 2 * ρ6 := (snorm_add_le _ _).trans (by linarith)
    set G : ZMod p → ℂ := fun k => H n1 n1' (t - k) with hG
    have hGb : ∀ k, ‖G k‖ ≤ 1 := fun k => by
      simp only [hG, hH, norm_mul, norm_ec, mul_one, Complex.norm_conj]
      have := hu1 n1; have := hu1 n1'; have := hg2 (t - k - n1); have := hg2 (t - k - n1')
      have a1 := mul_le_one₀ (hu1 n1) (norm_nonneg _) (hu1 n1')
      have a2 := mul_le_one₀ (hg2 (t - k - n1)) (norm_nonneg _) (hg2 (t - k - n1'))
      exact mul_le_one₀ a1 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) a2
    -- reindex `m₁ = t - k`
    have e1 : ∑ m1, (regP T ρ5 m1 : ℂ) * H n1 n1' m1 = ∑ k, (regP T ρ5 k : ℂ) * G (k + t) := by
      have e : ∑ m1, (regP T ρ5 m1 : ℂ) * H n1 n1' m1 =
          ∑ k, (regP T ρ5 (t - k) : ℂ) * H n1 n1' (t - k) :=
        (Fintype.sum_equiv (Equiv.subLeft t) _ _ (fun k => by simp)).symm
      rw [e]
      have e' : ∑ k, (regP T ρ5 (t - k) : ℂ) * H n1 n1' (t - k) =
          ∑ k, (regP T ρ5 (k - t) : ℂ) * G k := by
        refine sum_congr rfl fun k _ => ?_
        rw [show t - k = -(k - t) by ring, regP_neg, show -(k - t) = t - k by ring]
      rw [e']
      exact (Fintype.sum_equiv (Equiv.addRight t) _ _ (fun k => by simp)).symm
    have hshift := regP_shift (Γ := T) (Γ' := T) subset_rfl hρ5 (by linarith : (0 : ℝ) ≤ 2 * ρ6)
      (by linarith) ((mem_bohr_iff_snorm (by linarith)).2 hst) G hGb
    rw [one_mul] at hshift
    -- the phase identity on the support
    have e2 : ∑ k, (regP T ρ5 k : ℂ) * G k =
        ∑ k, (regP T ρ5 k : ℂ) * (b3 n1 k * b4 n1' k * ec (X n1 n1')) := by
      refine sum_congr rfl fun k _ => ?_
      by_cases hk : regP T ρ5 k = 0
      · simp [hk]
      · have hsk : snorm T k ≤ ρ5 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ5.le hk) hρ5.le
        have hsn : ∀ n, snorm T n ≤ ρ6 → Ξ n (t - k) = Ξ n n1 + Ξ n n1' - Ξ n k := by
          intro n hn
          have hadd := hΞ2 n (by linarith)
          have hk2 : snorm T (-k) ≤ ρ5 := by rw [snorm_neg]; exact hsk
          have a1 : Ξ n (t + -k) = Ξ n t + Ξ n (-k) := hadd t (-k) (by linarith)
          have a2 : Ξ n t = Ξ n n1 + Ξ n n1' := hadd n1 n1' (by linarith)
          have a3 : Ξ n (-k) = -Ξ n k := hadd.map_neg k (by linarith)
          rw [sub_eq_add_neg, a1, a2, a3]
          abel
        congr 1
        simp only [hG, hH, hb3, hb4, hX]
        rw [hsn n1 hs1, hsn n1' hs1', show t - k - n1 = n1' - k by rw [ht]; ring,
          show t - k - n1' = n1 - k by rw [ht]; ring]
        have e3 : Ξ n1 n1 + Ξ n1 n1' - Ξ n1 k - (Ξ n1' n1 + Ξ n1' n1' - Ξ n1' k) =
            (Ξ n1 n1 - Ξ n1 k) + (Ξ n1' k - Ξ n1' n1') + (Ξ n1 n1' - Ξ n1' n1) := by abel
        rw [e3, ec_add, ec_add]
        ring
    rw [e1, ← e2]
    calc _ ≤ 50 * T.card * (2 * ρ6) / ρ5 := hshift
      _ = 100 * T.card * ρ6 / ρ5 := by ring
  -- combine
  set V : ZMod p → ℂ := fun k => ∑ n1, ∑ n1', (regP T ρ6 n1 : ℂ) * (regP T ρ6 n1' : ℂ) *
    (b3 n1 k * b4 n1' k * ec (X n1 n1')) with hV
  have hmain : ∑ n1, ∑ n1', ((regP T ρ6 n1 * regP T ρ6 n1' : ℝ) : ℂ) *
      ∑ k, (regP T ρ5 k : ℂ) * (b3 n1 k * b4 n1' k * ec (X n1 n1')) =
      ∑ k, (regP T ρ5 k : ℂ) * V k := by
    simp only [hV, mul_sum]
    symm
    rw [sum_comm]
    refine sum_congr rfl fun n1 _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun n1' _ => sum_congr rfl fun k _ => ?_
    push_cast; ring
  have hdiff : ‖∑ n1, ∑ n1', ((regP T ρ6 n1 * regP T ρ6 n1' : ℝ) : ℂ) *
      ∑ m1, (regP T ρ5 m1 : ℂ) * H n1 n1' m1 - ∑ k, (regP T ρ5 k : ℂ) * V k‖ ≤
      100 * T.card * ρ6 / ρ5 := by
    rw [← hmain, ← sum_sub_distrib]
    simp_rw [← sum_sub_distrib, ← mul_sub]
    have hpair := prod_dist hP6.1 hP6.2
    calc ‖∑ n1, ∑ n1', ((regP T ρ6 n1 * regP T ρ6 n1' : ℝ) : ℂ) *
          (∑ m1, (regP T ρ5 m1 : ℂ) * H n1 n1' m1 -
            ∑ k, (regP T ρ5 k : ℂ) * (b3 n1 k * b4 n1' k * ec (X n1 n1')))‖
        ≤ ∑ n1, ∑ n1', regP T ρ6 n1 * regP T ρ6 n1' * (100 * T.card * ρ6 / ρ5) := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun n1 _ => (norm_sum_le _ _).trans
            (sum_le_sum fun n1' _ => ?_))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (hP6.1 n1) (hP6.1 n1'))]
          by_cases h1 : regP T ρ6 n1 = 0
          · simp [h1]
          by_cases h1' : regP T ρ6 n1' = 0
          · simp [h1']
          exact mul_le_mul_of_nonneg_left (hcv n1 n1' h1 h1')
            (mul_nonneg (hP6.1 n1) (hP6.1 n1'))
      _ = 100 * T.card * ρ6 / ρ5 := by
          have : ∀ n1, ∑ n1', regP T ρ6 n1 * regP T ρ6 n1' * (100 * T.card * ρ6 / ρ5) =
              regP T ρ6 n1 * (100 * T.card * ρ6 / ρ5) := fun n1 => by
            rw [← sum_mul, ← mul_sum, hP6.2, mul_one]
          rw [sum_congr rfl (fun n1 _ => this n1), ← sum_mul, hP6.2, one_mul]
  have hlow : δ ≤ ∑ k, regP T ρ5 k * ‖V k‖ := by
    have h1 : c ^ 2 ≤ ‖∑ n1, ∑ n1', ((regP T ρ6 n1 * regP T ρ6 n1' : ℝ) : ℂ) *
        ∑ m1, (regP T ρ5 m1 : ℂ) * H n1 n1' m1‖ := by
      rw [← hexp, Complex.norm_real, Real.norm_eq_abs]
      exact hc3.trans (le_abs_self _)
    have h2 := norm_sub_norm_le (∑ n1, ∑ n1', ((regP T ρ6 n1 * regP T ρ6 n1' : ℝ) : ℂ) *
        ∑ m1, (regP T ρ5 m1 : ℂ) * H n1 n1' m1) (∑ k, (regP T ρ5 k : ℂ) * V k)
    have h3 : ‖∑ k, (regP T ρ5 k : ℂ) * V k‖ ≤ ∑ k, regP T ρ5 k * ‖V k‖ :=
      (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP5.1 k)]))
    rw [hδdef]; linarith
  obtain ⟨k, -, hk⟩ := exists_pos_ge hP5.1 hP5.2 (fun k => ‖V k‖) hlow
  -- Step 4: the tail
  have hc1' : c ≤ 1 := by
    refine hc.trans ?_
    calc ∑ n1, regP T ρ6 n1 * ‖A n1‖ ^ 2 ≤ ∑ n1, regP T ρ6 n1 * 1 :=
          sum_le_sum fun n1 _ => mul_le_mul_of_nonneg_left
            (by have := hA1 n1; have := norm_nonneg (A n1); nlinarith) (hP6.1 n1)
      _ = 1 := by simp [hP6.2]
  have hδ1 : δ ≤ 1 := by
    have : c ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ 100 * T.card * ρ6 / ρ5 := by positivity
    rw [hδdef]; linarith
  have H1 : ∀ m, snorm T m ≤ 2 * ρ6 → AddOn T (2 * ρ6) (fun n => X n m) := fun m hm =>
    ((hΞ1 m).sub (hΞ2 m (by linarith))).mono (by linarith)
  have H2 : ∀ n, snorm T n ≤ 2 * ρ6 → AddOn T (2 * ρ6) (fun m => X n m) := fun n hn =>
    ((hΞ2 n (by linarith)).sub (hΞ1 n)).mono (by linarith)
  exact bilin_tail hp hT hρ6 le_rfl H1 H2 (fun r => b3 r k) (fun h => b4 h k)
    (fun r => hb3b r k) (fun h => hb4b h k) hδ hδ1 hk

end

end GT
end File_GT_U3S8b

section File_GT_U3S9a
/-!
# Local inverse `U³`, ninth step: algebra of the bilinear form

The bilinear expansion used in Green–Tao, §9 (ninth step), and the local quadraticity of the
resulting phase.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

section bilin

variable {T : Finset (ZMod p)} {ρA : ℝ} {Ξ : ZMod p → ZMod p → UnitAddCircle}
  (hΞ1 : ∀ m, AddOn T ρA (fun n => Ξ n m))
  (hΞ2 : ∀ n, snorm T n ≤ ρA → AddOn T ρA (fun m => Ξ n m))
include hΞ1 hΞ2

/-- The diagonal of a bilinear form, plus a linear form, is locally quadratic. -/
lemma lq_diag_lin {r : ℝ} (hr : 0 ≤ r) (h8 : 8 * r ≤ ρA) {L : ZMod p → UnitAddCircle}
    (hL : AddOn T ρA L) : LocQuad (sBohr T 0 r) (fun m => Ξ m m + L m) := by
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have mem : ∀ x : ZMod p, x ∈ sBohr T 0 r → snorm T x ≤ r := fun x hx => by
    have := (mem_sBohr hr).1 hx; rwa [sub_zero] at this
  have sn := mem n m0
  have sh : ∀ h : ZMod p, n + h ∈ sBohr T 0 r → snorm T h ≤ 2 * r := fun h hh => by
    have := mem _ hh
    calc snorm T h = snorm T ((n + h) - n) := by rw [add_sub_cancel_left]
      _ ≤ snorm T (n + h) + snorm T n := snorm_sub_le _ _
      _ ≤ 2 * r := by linarith
  have s1 := sh h1 m1
  have s2 := sh h2 m2
  have s3 := sh h3 m3
  -- the key identity `D(y + h) = D(y) + D(h) + Ξ(y,h) + Ξ(h,y)`
  have key : ∀ y h : ZMod p, snorm T y ≤ 2 * r → snorm T h ≤ 2 * r →
      Ξ (y + h) (y + h) = Ξ y y + Ξ h h + (Ξ y h + Ξ h y) := by
    intro y h hy hh
    have a1 : Ξ (y + h) (y + h) = Ξ y (y + h) + Ξ h (y + h) := hΞ1 (y + h) y h (by linarith)
    have a2 : Ξ y (y + h) = Ξ y y + Ξ y h := hΞ2 y (by linarith) y h (by linarith)
    have a3 : Ξ h (y + h) = Ξ h y + Ξ h h := hΞ2 h (by linarith) y h (by linarith)
    rw [a1, a2, a3]; abel
  set Lh : ZMod p → UnitAddCircle := fun y => Ξ y h1 + Ξ h1 y with hLh
  have hLadd : AddOn T ρA Lh := (hΞ1 h1).add (hΞ2 h1 (by linarith))
  have e23 := mem _ m23
  have e2 := mem _ m2
  have e3 := mem _ m3
  have k1 := key (n + h2 + h3) h1 (by linarith) s1
  have k2 := key (n + h2) h1 (by linarith) s1
  have k3 := key (n + h3) h1 (by linarith) s1
  have k4 := key n h1 (by linarith) s1
  have l1 : Lh (n + h2 + h3) = Lh (n + h2) + Lh h3 := hLadd _ _ (by linarith)
  have l2 : Lh (n + h3) = Lh n + Lh h3 := hLadd _ _ (by linarith)
  have la1 : L (n + h2 + h3 + h1) = L (n + h2 + h3) + L h1 := hL _ _ (by linarith)
  have la2 : L (n + h2 + h1) = L (n + h2) + L h1 := hL _ _ (by linarith)
  have la3 : L (n + h3 + h1) = L (n + h3) + L h1 := hL _ _ (by linarith)
  have la4 : L (n + h1) = L n + L h1 := hL _ _ (by linarith)
  try simp only
  rw [show n + h1 + h2 + h3 = n + h2 + h3 + h1 by ring, show n + h1 + h2 = n + h2 + h1 by ring,
    show n + h1 + h3 = n + h3 + h1 by ring]
  rw [k1, k2, k3, k4, la1, la2, la3, la4]
  simp only [hLh] at l1 l2
  rw [l1, l2]
  abel

/-- The bilinear expansion of the ninth step. -/
lemma xi_expand {N : ℕ} {n1 m1 n2 m2 : ZMod p}
    (hs : snorm T n1 + snorm T m1 + N * (snorm T n2 + snorm T m2) ≤ ρA) (hN : 1 ≤ N) :
    Ξ (n1 + (N : ZMod p) * n2) (m1 + (N : ZMod p) * m2) =
      Ξ n1 m1 + N • Ξ n2 m1 + N • Ξ n1 m2 +
        (N * N) • Ξ n2 m2 := by
  have h0n1 := snorm_nonneg (S := T) n1
  have h0m1 := snorm_nonneg (S := T) m1
  have h0n2 := snorm_nonneg (S := T) n2
  have h0m2 := snorm_nonneg (S := T) m2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have sN2 := snorm_nsmul_le (S := T) N n2
  have sM2 := snorm_nsmul_le (S := T) N m2
  have hNn : (N : ℝ) * snorm T n2 ≤ ρA := by nlinarith
  have hNm : (N : ℝ) * snorm T m2 ≤ ρA := by nlinarith
  have a1 : Ξ (n1 + (N : ZMod p) * n2) (m1 + (N : ZMod p) * m2) =
      Ξ n1 (m1 + (N : ZMod p) * m2) + Ξ ((N : ZMod p) * n2) (m1 + (N : ZMod p) * m2) :=
    hΞ1 _ _ _ (by nlinarith)
  have a2 : Ξ ((N : ZMod p) * n2) (m1 + (N : ZMod p) * m2) = N • Ξ n2 (m1 + (N : ZMod p) * m2) :=
    (hΞ1 _).map_nsmul N n2 hNn
  have hn1 : snorm T n1 ≤ ρA := by nlinarith
  have hn2 : snorm T n2 ≤ ρA := by nlinarith
  have b1 : Ξ n1 (m1 + (N : ZMod p) * m2) = Ξ n1 m1 + N • Ξ n1 m2 := by
    have := (hΞ2 n1 hn1) m1 ((N : ZMod p) * m2) (by nlinarith)
    (try simp only at this)
    rw [this, (hΞ2 n1 hn1).map_nsmul N m2 hNm]
  have b2 : Ξ n2 (m1 + (N : ZMod p) * m2) = Ξ n2 m1 + N • Ξ n2 m2 := by
    have := (hΞ2 n2 hn2) m1 ((N : ZMod p) * m2) (by nlinarith)
    (try simp only at this)
    rw [this, (hΞ2 n2 hn2).map_nsmul N m2 hNm]
  rw [a1, a2, b1, b2, nsmul_add, mul_nsmul']
  abel

/-- Polarisation of the diagonal. -/
lemma xi_polar {n2 m2 : ZMod p} (hs : 2 * (snorm T n2 + snorm T m2) ≤ ρA) :
    2 • Ξ n2 m2 = Ξ n2 n2 + Ξ m2 m2 - Ξ (n2 - m2) (n2 - m2) + (Ξ n2 m2 - Ξ m2 n2) := by
  have h0n2 := snorm_nonneg (S := T) n2
  have h0m2 := snorm_nonneg (S := T) m2
  have hnm : snorm T (n2 - m2) ≤ snorm T n2 + snorm T m2 := snorm_sub_le _ _
  have a1 : Ξ (n2 - m2) (n2 - m2) = Ξ n2 (n2 - m2) + Ξ (-m2) (n2 - m2) := by
    rw [sub_eq_add_neg n2 m2]
    exact hΞ1 _ _ _ (by rw [snorm_neg]; linarith)
  have a2 : Ξ (-m2) (n2 - m2) = -Ξ m2 (n2 - m2) := (hΞ1 _).map_neg m2 (by linarith)
  have b : ∀ x : ZMod p, snorm T x ≤ ρA → Ξ x (n2 - m2) = Ξ x n2 - Ξ x m2 := fun x hx => by
    rw [sub_eq_add_neg n2 m2]
    have := (hΞ2 x hx) n2 (-m2) (by rw [snorm_neg]; linarith)
    (try simp only at this)
    rw [this, (hΞ2 x hx).map_neg m2 (by linarith)]
    abel
  rw [a1, a2, b n2 (by linarith), b m2 (by linarith), two_nsmul]
  abel

end bilin

/-- Reflection preserves local quadraticity on a centred Bohr set. -/
lemma LocQuad.neg_arg {T : Finset (ZMod p)} {r : ℝ} (hr : 0 ≤ r) {M : Type*} [AddCommGroup M]
    {ψ : ZMod p → M} (hL : LocQuad (sBohr T 0 r) ψ) :
    LocQuad (sBohr T 0 r) (fun m => ψ (-m)) := by
  have mem : ∀ x : ZMod p, x ∈ sBohr T 0 r → -x ∈ sBohr T 0 r := fun x hx => by
    rw [mem_sBohr hr, sub_zero] at hx ⊢; rwa [snorm_neg]
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have := hL (-n) (-h1) (-h2) (-h3) (mem _ m0) (by rw [← neg_add]; exact mem _ m1)
    (by rw [← neg_add]; exact mem _ m2) (by rw [← neg_add]; exact mem _ m3)
    (by rw [← neg_add, ← neg_add]; exact mem _ m12) (by rw [← neg_add, ← neg_add]; exact mem _ m13)
    (by rw [← neg_add, ← neg_add]; exact mem _ m23)
    (by rw [← neg_add, ← neg_add, ← neg_add]; exact mem _ m123)
  simp only [← neg_add] at this
  exact this

end

end GT
end File_GT_U3S9a

section File_GT_U3S9b
/-!
# Local inverse `U³`, ninth step: the analytic lemmas

Translation and pigeonholing, the double Cauchy–Schwarz argument producing a local `U²` norm,
and the application of the local inverse `U²` theorem (Green–Tao, §9, ninth step).
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma sq_le_sq_add_two_norm {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 + 2 * ‖u - v‖ := by
  have h1 : ‖u‖ - ‖v‖ ≤ ‖u - v‖ := norm_sub_norm_le u v
  have h2 : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u - v)]

lemma norm_wavg_le_one {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (F : α → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) : ‖∑ x, (P x : ℂ) * F x‖ ≤ 1 :=
  norm_wavg_le hP hP1 F fun x _ => hF x

/-- Translating both inner variables and pigeonholing (first part of the ninth step). -/
theorem shift9 {T : Finset (ZMod p)} {P0 : ZMod p → ℝ} (hP0 : ∀ x, 0 ≤ P0 x)
    (hP01 : ∑ x, P0 x = 1) {ρ5 ρ6 ρ9 ρ10 : ℝ} (hρ5 : 0 < ρ5) (hρ6 : 0 < ρ6) (hρ9 : 0 < ρ9)
    (hρ10 : 0 < ρ10) (N : ℕ) (h10 : 4 * (N * ρ10) ≤ ρ5) (h9 : 4 * (N * ρ9) ≤ ρ6)
    (Φ : ZMod p → ZMod p → ZMod p → ℂ) (hΦ : ∀ a b c, ‖Φ a b c‖ ≤ 1) {c : ℝ}
    (hc : c ≤ ∑ n0, P0 n0 * ∑ n1, regP T ρ6 n1 * ‖∑ m1, (regP T ρ5 m1 : ℂ) * Φ n0 n1 m1‖ ^ 2) :
    ∃ n1 m1, regP T ρ6 n1 ≠ 0 ∧ regP T ρ5 m1 ≠ 0 ∧
      c - (2 * (50 * T.card * (N * ρ10) / ρ5) + 50 * T.card * (N * ρ9) / ρ6) ≤
        ∑ n0, P0 n0 * ∑ n2, regP T ρ9 n2 *
          ‖∑ m2, (regP T ρ10 m2 : ℂ) * Φ n0 (n1 + (N : ZMod p) * n2) (m1 + (N : ZMod p) * m2)‖ ^ 2 := by
  have hP5 := regP_isDist T hρ5.le
  have hP6 := regP_isDist T hρ6.le
  have hP9 := regP_isDist T hρ9.le
  have hP10 := regP_isDist T hρ10.le
  set e1 := 50 * T.card * (N * ρ10) / ρ5 with he1
  set e2 := 50 * T.card * (N * ρ9) / ρ6 with he2
  set A : ZMod p → ZMod p → ℂ := fun n0 x => ∑ m1, (regP T ρ5 m1 : ℂ) * Φ n0 x m1 with hA
  set A' : ZMod p → ZMod p → ℂ := fun n0 x =>
    ∑ m1, (regP T ρ5 m1 : ℂ) * ∑ m2, (regP T ρ10 m2 : ℂ) * Φ n0 x (m1 + (N : ZMod p) * m2)
    with hA'
  have hAb : ∀ n0 x, ‖A n0 x‖ ≤ 1 := fun n0 x => norm_wavg_le_one hP5.1 hP5.2 _ fun _ => hΦ _ _ _
  have hA'b : ∀ n0 x, ‖A' n0 x‖ ≤ 1 := fun n0 x =>
    norm_wavg_le_one hP5.1 hP5.2 _ fun _ => norm_wavg_le_one hP10.1 hP10.2 _ fun _ => hΦ _ _ _
  -- shifting `m₁`
  have hAA : ∀ n0 x, ‖A' n0 x - A n0 x‖ ≤ e1 := by
    intro n0 x
    have e : A' n0 x = ∑ m2, (regP T ρ10 m2 : ℂ) *
        ∑ m1, (regP T ρ5 m1 : ℂ) * Φ n0 x (m1 + (N : ZMod p) * m2) := by
      simp only [hA', mul_sum]; rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [e]
    refine norm_wavg_sub_le hP10.1 hP10.2 _ _ fun m2 hm2 => ?_
    have hs : snorm T ((N : ZMod p) * m2) ≤ N * ρ10 :=
      (snorm_nsmul_le N m2).trans (mul_le_mul_of_nonneg_left
        (snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ10.le hm2) hρ10.le) (Nat.cast_nonneg _))
    have := regP_shift (Γ := T) (Γ' := T) subset_rfl hρ5 (by positivity) h10
      ((mem_bohr_iff_snorm (by positivity)).2 hs) (fun m1 => Φ n0 x m1) (fun _ => hΦ _ _ _)
    rw [one_mul] at this
    exact this
  have step1 : ∀ n0, ∑ n1, regP T ρ6 n1 * ‖A n0 n1‖ ^ 2 ≤
      ∑ n1, regP T ρ6 n1 * ‖A' n0 n1‖ ^ 2 + 2 * e1 := by
    intro n0
    have : ∑ n1, regP T ρ6 n1 * ‖A n0 n1‖ ^ 2 ≤
        ∑ n1, regP T ρ6 n1 * (‖A' n0 n1‖ ^ 2 + 2 * e1) := by
      refine sum_le_sum fun n1 _ => mul_le_mul_of_nonneg_left ?_ (hP6.1 n1)
      have := sq_le_sq_add_two_norm (hAb n0 n1) (hA'b n0 n1)
      rw [norm_sub_rev] at this
      linarith [hAA n0 n1]
    simp only [mul_add, sum_add_distrib, ← sum_mul, hP6.2, one_mul] at this
    exact this
  -- shifting `n₁`
  have step2 : ∀ n0, ∑ n1, regP T ρ6 n1 * ‖A' n0 n1‖ ^ 2 ≤
      ∑ n2, regP T ρ9 n2 * ∑ n1, regP T ρ6 n1 * ‖A' n0 (n1 + (N : ZMod p) * n2)‖ ^ 2 + e2 := by
    intro n0
    have hpt : ∀ n2, regP T ρ9 n2 ≠ 0 → ∑ n1, regP T ρ6 n1 * ‖A' n0 n1‖ ^ 2 ≤
        ∑ n1, regP T ρ6 n1 * ‖A' n0 (n1 + (N : ZMod p) * n2)‖ ^ 2 + e2 := by
      intro n2 hn2
      have hs : snorm T ((N : ZMod p) * n2) ≤ N * ρ9 :=
        (snorm_nsmul_le N n2).trans (mul_le_mul_of_nonneg_left
          (snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ9.le hn2) hρ9.le) (Nat.cast_nonneg _))
      have := shift_real (Γ := T) (Γ' := T) subset_rfl hρ6 h9 hs
        (fun x => ‖A' n0 x‖ ^ 2) (fun x => by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact pow_le_one₀ (norm_nonneg _) (hA'b n0 x))
      rw [one_mul] at this
      linarith [(abs_le.1 this).1]
    calc ∑ n1, regP T ρ6 n1 * ‖A' n0 n1‖ ^ 2 =
        ∑ n2, regP T ρ9 n2 * ∑ n1, regP T ρ6 n1 * ‖A' n0 n1‖ ^ 2 := by
          rw [← sum_mul, hP9.2, one_mul]
      _ ≤ ∑ n2, regP T ρ9 n2 *
          (∑ n1, regP T ρ6 n1 * ‖A' n0 (n1 + (N : ZMod p) * n2)‖ ^ 2 + e2) := by
          refine sum_le_sum fun n2 _ => ?_
          by_cases hn2 : regP T ρ9 n2 = 0
          · simp [hn2]
          · exact mul_le_mul_of_nonneg_left (hpt n2 hn2) (hP9.1 n2)
      _ = _ := by simp only [mul_add, sum_add_distrib, ← sum_mul, hP9.2, one_mul]
  -- Cauchy–Schwarz in `m₁`
  set B : ZMod p → ZMod p → ZMod p → ZMod p → ℂ := fun n0 n1 m1 n2 =>
    ∑ m2, (regP T ρ10 m2 : ℂ) * Φ n0 (n1 + (N : ZMod p) * n2) (m1 + (N : ZMod p) * m2) with hB
  have step3 : ∀ n0 n1 n2, ‖A' n0 (n1 + (N : ZMod p) * n2)‖ ^ 2 ≤
      ∑ m1, regP T ρ5 m1 * ‖B n0 n1 m1 n2‖ ^ 2 := fun n0 n1 n2 =>
    norm_wsum_sq_le hP5.1 hP5.2 _
  have hmain : c - (2 * e1 + e2) ≤ ∑ n1, ∑ m1, regP T ρ6 n1 * regP T ρ5 m1 *
      ∑ n0, P0 n0 * ∑ n2, regP T ρ9 n2 * ‖B n0 n1 m1 n2‖ ^ 2 := by
    have h1 : c - (2 * e1 + e2) ≤ ∑ n0, P0 n0 * ∑ n2, regP T ρ9 n2 * ∑ n1, regP T ρ6 n1 *
        ∑ m1, regP T ρ5 m1 * ‖B n0 n1 m1 n2‖ ^ 2 := by
      have : ∀ n0, ∑ n1, regP T ρ6 n1 * ‖A n0 n1‖ ^ 2 - (2 * e1 + e2) ≤
          ∑ n2, regP T ρ9 n2 * ∑ n1, regP T ρ6 n1 *
            ∑ m1, regP T ρ5 m1 * ‖B n0 n1 m1 n2‖ ^ 2 := by
        intro n0
        have s3 : ∑ n2, regP T ρ9 n2 * ∑ n1, regP T ρ6 n1 * ‖A' n0 (n1 + (N : ZMod p) * n2)‖ ^ 2 ≤
            ∑ n2, regP T ρ9 n2 * ∑ n1, regP T ρ6 n1 *
              ∑ m1, regP T ρ5 m1 * ‖B n0 n1 m1 n2‖ ^ 2 :=
          sum_le_sum fun n2 _ => mul_le_mul_of_nonneg_left (sum_le_sum fun n1 _ =>
            mul_le_mul_of_nonneg_left (step3 n0 n1 n2) (hP6.1 n1)) (hP9.1 n2)
        linarith [step1 n0, step2 n0]
      calc c - (2 * e1 + e2) ≤ ∑ n0, P0 n0 * ∑ n1, regP T ρ6 n1 * ‖A n0 n1‖ ^ 2 -
            (2 * e1 + e2) := by linarith
        _ = ∑ n0, P0 n0 * (∑ n1, regP T ρ6 n1 * ‖A n0 n1‖ ^ 2 - (2 * e1 + e2)) := by
            simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP01, one_mul]
        _ ≤ _ := sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left (this n0) (hP0 n0)
    refine h1.trans (le_of_eq ?_)
    simp only [mul_sum]
    rw [sum4_perm]
    refine sum_congr rfl fun n1 _ => sum_congr rfl fun m1 _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun n0 _ => sum_congr rfl fun n2 _ => by ring
  obtain ⟨n1, m1, hn1, hm1, hge⟩ := exists_pair_ge hρ6.le hρ5.le _ hmain
  exact ⟨n1, m1, hn1, hm1, hge⟩

end

end GT
end File_GT_U3S9b

section File_GT_U3S9c
/-!
# Local inverse `U³`, ninth step: double Cauchy–Schwarz and the local inverse `U²` theorem
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma sum4_swap' {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (F : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d :=
        sum_congr rfl fun a _ => sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, F a b c d :=
        sum_congr rfl fun a _ => sum_congr rfl fun c _ => sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_comm

/-- The local `U²`-type average of `F` with outer variables distributed by `P` and inner ones
by `Q`. -/
def u2box (P Q : ZMod p → ℝ) (F : ZMod p → ℂ) : ℂ :=
  ∑ h0, ∑ h0', ∑ h1, ∑ h1', ((P h0 * P h0' * Q h1 * Q h1' : ℝ) : ℂ) *
    (F (h0 + h1) * conj (F (h0 + h1')) * conj (F (h0' + h1)) * F (h0' + h1'))

lemma box_identity (P Q : ZMod p → ℝ) (hQ : ∀ x, Q (-x) = Q x) (F : ZMod p → ℂ) :
    ((∑ m, ∑ m', Q m * Q m' *
      ‖∑ n, (P n : ℂ) * (F (n - m) * conj (F (n - m')))‖ ^ 2 : ℝ) : ℂ) = u2box P Q F := by
  set Z : ZMod p → ZMod p → ℂ := fun m m' =>
    ∑ n, (P n : ℂ) * (F (n - m) * conj (F (n - m'))) with hZ
  set K : ZMod p → ZMod p → ℂ := fun m m' => ∑ n, ∑ n', ((P n * P n' : ℝ) : ℂ) *
    (F (n + m) * conj (F (n + m')) * conj (F (n' + m)) * F (n' + m')) with hK
  have hb : ∀ m m', ((‖Z (-m) (-m')‖ ^ 2 : ℝ) : ℂ) = K m m' := by
    intro m m'
    rw [hZ]; simp only; rw [ofReal_norm_sq_wsum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => ?_
    simp only [sub_neg_eq_add, map_mul, RCLike.conj_conj]
    ring
  have hrefl : ∑ m, ∑ m', ((Q m * Q m' : ℝ) : ℂ) * ((‖Z m m'‖ ^ 2 : ℝ) : ℂ) =
      ∑ m, ∑ m', ((Q m * Q m' : ℝ) : ℂ) * ((‖Z (-m) (-m')‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun m => rfl)]
    refine sum_congr rfl fun m _ => ?_
    rw [← Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun m' => rfl)]
    refine sum_congr rfl fun m' _ => ?_
    simp only [Equiv.neg_apply, hQ]
  push_cast
  have e1 : ∑ m, ∑ m', (Q m : ℂ) * (Q m' : ℂ) * (‖Z m m'‖ : ℂ) ^ 2 =
      ∑ m, ∑ m', ((Q m * Q m' : ℝ) : ℂ) * ((‖Z m m'‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e1, hrefl]
  simp only [hb, hK, u2box, mul_sum]
  rw [sum4_swap']
  refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => sum_congr rfl fun m _ =>
    sum_congr rfl fun m' _ => ?_
  push_cast; ring

lemma norm_u2box_le_one {P Q : ZMod p → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (hQ : ∀ x, 0 ≤ Q x) (hQ1 : ∑ x, Q x = 1) (F : ZMod p → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    ‖u2box P Q F‖ ≤ 1 := by
  unfold u2box
  have hb : ∀ a b c d : ZMod p, ‖F (a + c) * conj (F (a + d)) * conj (F (b + c)) * F (b + d)‖ ≤ 1 :=
    fun a b c d => by
      simp only [norm_mul, Complex.norm_conj]
      have := hF (a + c); have := hF (a + d); have := hF (b + c); have := hF (b + d)
      have h1 := mul_le_one₀ (hF (a + c)) (norm_nonneg _) (hF (a + d))
      have h2 := mul_le_one₀ h1 (norm_nonneg _) (hF (b + c))
      exact mul_le_one₀ h2 (norm_nonneg _) (hF (b + d))
  have hsum : ∑ h0, ∑ h0', ∑ h1, ∑ h1', P h0 * P h0' * Q h1 * Q h1' = 1 := by
    simp only [← mul_sum, hQ1, mul_one, ← sum_mul, hP1, one_mul]
  calc _ ≤ ∑ h0, ∑ h0', ∑ h1, ∑ h1', P h0 * P h0' * Q h1 * Q h1' := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => (norm_sum_le _ _).trans
          (sum_le_sum fun b _ => (norm_sum_le _ _).trans (sum_le_sum fun c _ =>
            (norm_sum_le _ _).trans (sum_le_sum fun d _ => ?_))))
        have hw : 0 ≤ P a * P b * Q c * Q d :=
          mul_nonneg (mul_nonneg (mul_nonneg (hP a) (hP b)) (hQ c)) (hQ d)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
        exact mul_le_of_le_one_right hw (hb a b c d)
    _ = 1 := hsum

/-- The double Cauchy–Schwarz argument of the ninth step. -/
theorem cs9 {T : Finset (ZMod p)} {P0 : ZMod p → ℝ} (hP0 : ∀ x, 0 ≤ P0 x)
    (hP01 : ∑ x, P0 x = 1) {ρ9 ρ10 : ℝ} (hρ9 : 0 < ρ9) (hρ10 : 0 < ρ10)
    (F G : ZMod p → ZMod p → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ 1) (hG : ∀ a b, ‖G a b‖ ≤ 1) {c : ℝ}
    (hc0 : 0 ≤ c)
    (hc : c ≤ ∑ n0, P0 n0 * ∑ n2, regP T ρ9 n2 *
      ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F n0 (n2 - m2) * G n0 m2)‖ ^ 2) :
    c ^ 2 ≤ ∑ n0, P0 n0 * ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖ := by
  have hP9 := regP_isDist T hρ9.le
  have hP10 := regP_isDist T hρ10.le
  set Z : ZMod p → ZMod p → ZMod p → ℂ := fun n0 m m' =>
    ∑ n, (regP T ρ9 n : ℂ) * (F n0 (n - m) * conj (F n0 (n - m'))) with hZ
  set X : ZMod p → ℝ := fun n0 => ∑ n2, regP T ρ9 n2 *
    ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F n0 (n2 - m2) * G n0 m2)‖ ^ 2 with hX
  have hX0 : ∀ n0, 0 ≤ X n0 := fun n0 =>
    sum_nonneg fun _ _ => mul_nonneg (hP9.1 _) (sq_nonneg _)
  -- (i) expansion
  have hexp : ∀ n0, ((X n0 : ℝ) : ℂ) = ∑ m, ∑ m', ((regP T ρ10 m * regP T ρ10 m' : ℝ) : ℂ) *
      (G n0 m * conj (G n0 m') * Z n0 m m') := by
    intro n0
    simp only [hX, hZ]
    push_cast
    have e : ∀ n2, ((‖∑ m2, (regP T ρ10 m2 : ℂ) * (F n0 (n2 - m2) * G n0 m2)‖ : ℂ)) ^ 2 =
        ∑ m, ∑ m', ((regP T ρ10 m * regP T ρ10 m' : ℝ) : ℂ) *
          (F n0 (n2 - m) * G n0 m * conj (F n0 (n2 - m') * G n0 m')) := fun n2 => by
      have := ofReal_norm_sq_wsum (regP T ρ10) (fun m2 => F n0 (n2 - m2) * G n0 m2)
      push_cast at this ⊢
      rw [this]
    simp only [e, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m' _ => sum_congr rfl fun n _ => ?_
    simp only [map_mul]
    push_cast; ring
  -- (ii) the triangle inequality
  have hX1 : ∀ n0, X n0 ≤ ∑ m, ∑ m', regP T ρ10 m * regP T ρ10 m' * ‖Z n0 m m'‖ := by
    intro n0
    have : X n0 = ‖((X n0 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hX0 n0)]
    rw [this, hexp]
    refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => (norm_sum_le _ _).trans
      (sum_le_sum fun m' _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hP10.1 m) (hP10.1 m'))]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hP10.1 m) (hP10.1 m'))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := hG n0 m; have := hG n0 m'
    have h1 := mul_le_one₀ (hG n0 m) (norm_nonneg _) (hG n0 m')
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  -- (iii) Jensen
  have hX2 : ∀ n0, X n0 ^ 2 ≤ ∑ m, ∑ m', regP T ρ10 m * regP T ρ10 m' * ‖Z n0 m m'‖ ^ 2 := by
    intro n0
    have h1 := pow_le_pow_left₀ (hX0 n0) (hX1 n0) 2
    refine h1.trans ?_
    have e : ∀ m, ∑ m', regP T ρ10 m * regP T ρ10 m' * ‖Z n0 m m'‖ =
        regP T ρ10 m * ∑ m', regP T ρ10 m' * ‖Z n0 m m'‖ := fun m => by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    simp only [e]
    refine (sq_wavg_le _ hP10.1 hP10.2).trans (sum_le_sum fun m _ => ?_)
    have := sq_wavg_le (fun m' => ‖Z n0 m m'‖) hP10.1 hP10.2
    calc regP T ρ10 m * (∑ m', regP T ρ10 m' * ‖Z n0 m m'‖) ^ 2 ≤
        regP T ρ10 m * ∑ m', regP T ρ10 m' * ‖Z n0 m m'‖ ^ 2 :=
          mul_le_mul_of_nonneg_left this (hP10.1 m)
      _ = _ := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  -- (iv) the box identity
  have hX3 : ∀ n0, ∑ m, ∑ m', regP T ρ10 m * regP T ρ10 m' * ‖Z n0 m m'‖ ^ 2 =
      ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖ := by
    intro n0
    have hbi := box_identity (regP T ρ9) (regP T ρ10) (regP_neg T ρ10) (F n0)
    rw [← hbi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
      mul_nonneg (mul_nonneg (hP10.1 _) (hP10.1 _)) (sq_nonneg _)
  -- (v) combine
  have h1 : c ^ 2 ≤ (∑ n0, P0 n0 * X n0) ^ 2 := pow_le_pow_left₀ hc0 hc 2
  refine h1.trans ((sq_wavg_le _ hP0 hP01).trans (sum_le_sum fun n0 _ => ?_))
  exact mul_le_mul_of_nonneg_left ((hX2 n0).trans (le_of_eq (hX3 n0))) (hP0 n0)

/-- Popularity and the local inverse `U²` theorem in the ninth step. -/
theorem u2pop9 {T : Finset (ZMod p)} {P0 : ZMod p → ℝ} (hP0 : ∀ x, 0 ≤ P0 x)
    (hP01 : ∑ x, P0 x = 1) {ρ9 ρ10 : ℝ} (hρ10 : 0 < ρ10) (h4 : 4 * ρ10 ≤ ρ9)
    (F : ZMod p → ZMod p → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hsep : 7200 * T.card * ρ10 ≤ (c / 2) ^ 2 * ρ9)
    (hc : c ≤ ∑ n0, P0 n0 * ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖) :
    ∃ (β : ZMod p → ZMod p) (n2 : ZMod p), regP T ρ9 n2 ≠ 0 ∧
      c ^ 2 / 8 ≤ ∑ n0, P0 n0 *
        ‖∑ m2, (regP T ρ10 m2 : ℂ) * F n0 (n2 + m2) * ech (-(β n0 * m2))‖ := by
  have hρ9 : 0 < ρ9 := by linarith
  have hP9 := regP_isDist T hρ9.le
  have hP10 := regP_isDist T hρ10.le
  classical
  have hUb : ∀ n0, ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖ ≤ 1 := fun n0 =>
    norm_u2box_le_one hP9.1 hP9.2 hP10.1 hP10.2 _ (hF n0)
  have hpop := popular hP0 hP01 (fun n0 => ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖)
    (t := c / 2) (by linarith) hUb hc
  rw [one_mul] at hpop
  have hex : ∀ n0, ∃ β : ZMod p, c / 2 ≤ ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖ →
      c / 2 / 2 ≤ ∑ n2, regP T ρ9 n2 *
        ‖∑ m2, (regP T ρ10 m2 : ℂ) * F n0 (n2 + m2) * ech (-(β * m2))‖ ^ 2 := by
    intro n0
    by_cases h : c / 2 ≤ ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖
    · obtain ⟨β, hβ⟩ := loc_u2_bohr (S := T) hρ10 h4 hsep (by linarith) (F n0) (hF n0) h
      exact ⟨β, fun _ => hβ⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose β hβ using hex
  set Y : ZMod p → ZMod p → ℝ := fun n0 n2 =>
    ‖∑ m2, (regP T ρ10 m2 : ℂ) * F n0 (n2 + m2) * ech (-(β n0 * m2))‖ with hY
  have hYb : ∀ n0 n2, Y n0 n2 ≤ 1 := fun n0 n2 => by
    simp only [hY, mul_assoc]
    refine norm_wavg_le hP10.1 hP10.2 _ fun m2 _ => ?_
    rw [norm_mul, ech_eq_ec, norm_ec, mul_one]; exact hF _ _
  have hlow : c / 2 * (c / 2 / 2) ≤ ∑ n0, P0 n0 * ∑ n2, regP T ρ9 n2 * Y n0 n2 ^ 2 := by
    calc c / 2 * (c / 2 / 2) ≤ (∑ n0, P0 n0 * (if c / 2 ≤
          ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖ then 1 else 0)) * (c / 2 / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = ∑ n0, P0 n0 * ((if c / 2 ≤ ‖u2box (regP T ρ9) (regP T ρ10) (F n0)‖ then 1 else 0) *
          (c / 2 / 2)) := by rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ _ := by
          refine sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left ?_ (hP0 n0)
          split_ifs with h
          · rw [one_mul]; exact hβ n0 h
          · rw [zero_mul]; exact sum_nonneg fun _ _ => mul_nonneg (hP9.1 _) (sq_nonneg _)
  have hswap : ∑ n0, P0 n0 * ∑ n2, regP T ρ9 n2 * Y n0 n2 ^ 2 =
      ∑ n2, regP T ρ9 n2 * ∑ n0, P0 n0 * Y n0 n2 ^ 2 := by
    simp only [mul_sum]; rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [hswap] at hlow
  obtain ⟨n2, hn2, hge⟩ := exists_pos_ge hP9.1 hP9.2 _ hlow
  refine ⟨β, n2, hn2, ?_⟩
  have : ∑ n0, P0 n0 * Y n0 n2 ^ 2 ≤ ∑ n0, P0 n0 * Y n0 n2 :=
    sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left
      (by have := hYb n0 n2; have : 0 ≤ Y n0 n2 := norm_nonneg _; nlinarith) (hP0 n0)
  have e : c ^ 2 / 8 = c / 2 * (c / 2 / 2) := by ring
  linarith

end

end GT
end File_GT_U3S9c

section File_GT_U3S9d
/-!
# Local inverse `U³`, ninth step: assembly

From the correlation with a locally bilinear phase (seventh step) and the approximate symmetry
(eighth step), we derive the correlation with a locally quadratic phase of Theorem 8.1.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The function whose local `U²` norm is large in the ninth step. -/
def F9 (Ξ : ZMod p → ZMod p → UnitAddCircle) (f : ZMod p → ℂ) (q : ℕ) (a2 n0 u : ZMod p) : ℂ :=
  f (n0 + a2 - ((2 * q : ℕ) : ZMod p) * u) * ec (-((2 * q ^ 2) • Ξ u u))

/-- The companion function of the ninth step. -/
def G9 (Ξ : ZMod p → ZMod p → UnitAddCircle) (f : ZMod p → ℂ) (q : ℕ) (n1 m1 ξ1 n0 m : ZMod p) :
    ℂ :=
  conj (f (n0 + m1 + ((2 * q : ℕ) : ZMod p) * m)) *
    ec ((2 * q) • Ξ n1 m + (2 * q ^ 2) • Ξ m m -
      ZMod.toAddCircle (ξ1 * (((2 * q : ℕ) : ZMod p) * m)))

lemma norm_F9_le {Ξ : ZMod p → ZMod p → UnitAddCircle} {f : ZMod p → ℂ} (hf : ∀ x, ‖f x‖ ≤ 1)
    (q : ℕ) (a2 n0 u : ZMod p) : ‖F9 Ξ f q a2 n0 u‖ ≤ 1 := by
  rw [F9, norm_mul, norm_ec, mul_one]; exact hf _

lemma norm_G9_le {Ξ : ZMod p → ZMod p → UnitAddCircle} {f : ZMod p → ℂ} (hf : ∀ x, ‖f x‖ ≤ 1)
    (q : ℕ) (n1 m1 ξ1 n0 m : ZMod p) : ‖G9 Ξ f q n1 m1 ξ1 n0 m‖ ≤ 1 := by
  rw [G9, norm_mul, norm_ec, mul_one, Complex.norm_conj]; exact hf _

section phase

variable {T : Finset (ZMod p)} {ρA : ℝ} {Ξ : ZMod p → ZMod p → UnitAddCircle}
  (hΞ1 : ∀ m, AddOn T ρA (fun n => Ξ n m))
  (hΞ2 : ∀ n, snorm T n ≤ ρA → AddOn T ρA (fun m => Ξ n m))
include hΞ1 hΞ2

/-- The pointwise phase identity of the ninth step. -/
lemma phase9 (f : ZMod p → ℂ) {q : ℕ} (hq : 1 ≤ q) (a1 ξ1 n0 n1 m1 n2 m2 : ZMod p)
    (hs : snorm T n1 + snorm T m1 + (2 * q : ℕ) * (snorm T n2 + snorm T m2) ≤ ρA) :
    f (n0 + (m1 + ((2 * q : ℕ) : ZMod p) * m2) + a1 - (n1 + ((2 * q : ℕ) : ZMod p) * n2)) *
        conj (f (n0 + (m1 + ((2 * q : ℕ) : ZMod p) * m2))) *
        ec (Ξ (n1 + ((2 * q : ℕ) : ZMod p) * n2) (m1 + ((2 * q : ℕ) : ZMod p) * m2) -
          ZMod.toAddCircle (ξ1 * (m1 + ((2 * q : ℕ) : ZMod p) * m2))) =
      ec (Ξ n1 m1 - ZMod.toAddCircle (ξ1 * m1)) *
        ec ((2 * q) • Ξ n2 m1 + (2 * q ^ 2) • Ξ n2 n2) *
        (F9 Ξ f q (a1 + m1 - n1) n0 (n2 - m2) * G9 Ξ f q n1 m1 ξ1 n0 m2) *
        ec ((2 * q ^ 2) • (Ξ n2 m2 - Ξ m2 n2)) := by
  have hN : 1 ≤ 2 * q := by omega
  have h0n2 := snorm_nonneg (S := T) n2
  have h0m2 := snorm_nonneg (S := T) m2
  have h0n1 := snorm_nonneg (S := T) n1
  have h0m1 := snorm_nonneg (S := T) m1
  have hN' : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast hN
  have hexp := xi_expand hΞ1 hΞ2 (N := 2 * q) hs hN
  have h2N : (2 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * q)
  have hpol := xi_polar hΞ1 hΞ2 (n2 := n2) (m2 := m2)
    (by nlinarith [mul_le_mul_of_nonneg_right h2N (add_nonneg h0n2 h0m2)])
  have hphase : Ξ (n1 + ((2 * q : ℕ) : ZMod p) * n2) (m1 + ((2 * q : ℕ) : ZMod p) * m2) -
      ZMod.toAddCircle (ξ1 * (m1 + ((2 * q : ℕ) : ZMod p) * m2)) =
      (Ξ n1 m1 - ZMod.toAddCircle (ξ1 * m1)) + ((2 * q) • Ξ n2 m1 + (2 * q ^ 2) • Ξ n2 n2) +
        (-((2 * q ^ 2) • Ξ (n2 - m2) (n2 - m2))) +
        ((2 * q) • Ξ n1 m2 + (2 * q ^ 2) • Ξ m2 m2 -
          ZMod.toAddCircle (ξ1 * (((2 * q : ℕ) : ZMod p) * m2))) +
        (2 * q ^ 2) • (Ξ n2 m2 - Ξ m2 n2) := by
    rw [hexp, mul_add, map_add]
    have e : ((2 * q) * (2 * q)) • Ξ n2 m2 = (2 * q ^ 2) • (2 • Ξ n2 m2) := by
      rw [← mul_nsmul']; congr 1; ring
    rw [e, hpol]
    module
  rw [hphase, ec_add, ec_add, ec_add, ec_add]
  simp only [F9, G9]
  have ef : n0 + (m1 + ((2 * q : ℕ) : ZMod p) * m2) + a1 - (n1 + ((2 * q : ℕ) : ZMod p) * n2) =
      n0 + (a1 + m1 - n1) - ((2 * q : ℕ) : ZMod p) * (n2 - m2) := by ring
  have eg : n0 + (m1 + ((2 * q : ℕ) : ZMod p) * m2) = n0 + m1 + ((2 * q : ℕ) : ZMod p) * m2 := by
    ring
  rw [ef, eg]
  ring

/-- The diagonal of `Ξ` at a sum. -/
lemma xi_diag_add {y h : ZMod p} (hs : 2 * (snorm T y + snorm T h) ≤ ρA) :
    Ξ (y + h) (y + h) = Ξ y y + (Ξ h h + (Ξ y h + Ξ h y)) := by
  have h0 := snorm_nonneg (S := T) y
  have h1 := snorm_nonneg (S := T) h
  have a1 : Ξ (y + h) (y + h) = Ξ y (y + h) + Ξ h (y + h) := hΞ1 (y + h) y h (by linarith)
  have a2 : Ξ y (y + h) = Ξ y y + Ξ y h := hΞ2 y (by linarith) y h (by linarith)
  have a3 : Ξ h (y + h) = Ξ h y + Ξ h h := hΞ2 h (by linarith) y h (by linarith)
  rw [a1, a2, a3]; abel

end phase

set_option maxHeartbeats 4000000 in
/-- **Ninth step, first half**: translating, pigeonholing, expanding the bilinear phase and
removing the antisymmetric part. -/
theorem final9a {S T : Finset (ZMod p)} (hST : S ⊆ T) {ρ0 ρA ρ5 ρ6 ρ9 ρ10 σa : ℝ}
    (hρ5 : 0 < ρ5) (hρ6 : 0 < ρ6) (hρ9 : 0 < ρ9) (hρ10 : 0 < ρ10)
    {Ξ : ZMod p → ZMod p → UnitAddCircle}
    (hΞ1 : ∀ m, AddOn T ρA (fun n => Ξ n m))
    (hΞ2 : ∀ n, snorm T n ≤ ρA → AddOn T ρA (fun m => Ξ n m))
    {q : ℕ} (hq1 : 1 ≤ q) {Kq : ℝ} (hKq : 0 ≤ Kq)
    (hq : ∀ n m, snorm T n ≤ ρ9 → snorm T m ≤ ρ10 →
      ‖q • (Ξ n m - Ξ m n)‖ ≤ Kq * snorm T n * snorm T m)
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (a1 ξ1 : ZMod p) (ha1 : snorm S a1 ≤ σa) {c7 : ℝ}
    (hc7 : c7 ≤ ∑ n0, regP S ρ0 n0 * ∑ n1, regP T ρ6 n1 * ‖∑ m1, (regP T ρ5 m1 : ℂ) *
      (f (n0 + m1 + a1 - n1) * conj (f (n0 + m1)) *
        ec (Ξ n1 m1 - ZMod.toAddCircle (ξ1 * m1)))‖ ^ 2)
    (hρ0 : 0 ≤ ρ0)
    (h10 : 4 * (((2 * q : ℕ) : ℝ) * ρ10) ≤ ρ5) (h9 : 4 * (((2 * q : ℕ) : ℝ) * ρ9) ≤ ρ6)
    (hA : ρ6 + ρ5 + ((2 * q : ℕ) : ℝ) * (ρ9 + ρ10) ≤ ρA) :
    ∃ (a2 : ZMod p) (G : ZMod p → ZMod p → ℂ), (∀ a b, ‖G a b‖ ≤ 1) ∧
      snorm S a2 ≤ σa + ρ5 + ρ6 ∧
      c7 - (2 * (50 * T.card * (((2 * q : ℕ) : ℝ) * ρ10) / ρ5) +
          50 * T.card * (((2 * q : ℕ) : ℝ) * ρ9) / ρ6) -
        2 * (2 * Real.pi * (((2 * q : ℕ) : ℝ) * (Kq * ρ9 * ρ10))) ≤
        ∑ n0, regP S ρ0 n0 * ∑ n2, regP T ρ9 n2 *
          ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F9 Ξ f q a2 n0 (n2 - m2) * G n0 m2)‖ ^ 2 := by
  have hP0 := regP_isDist S hρ0
  have hP9 := regP_isDist T hρ9.le
  have hP10 := regP_isDist T hρ10.le
  set N : ℕ := 2 * q with hNdef
  set Φ : ZMod p → ZMod p → ZMod p → ℂ := fun n0 x y =>
    f (n0 + y + a1 - x) * conj (f (n0 + y)) * ec (Ξ x y - ZMod.toAddCircle (ξ1 * y)) with hΦ
  have hΦb : ∀ a b c, ‖Φ a b c‖ ≤ 1 := fun a b c => by
    simp only [hΦ, norm_mul, norm_ec, mul_one, Complex.norm_conj]
    exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
  obtain ⟨n1, m1, hn1, hm1, hsh⟩ := shift9 hP0.1 hP0.2 hρ5 hρ6 hρ9 hρ10 N h10 h9 Φ hΦb hc7
  have hsn1 : snorm T n1 ≤ ρ6 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ6.le hn1) hρ6.le
  have hsm1 : snorm T m1 ≤ ρ5 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ5.le hm1) hρ5.le
  refine ⟨a1 + m1 - n1, G9 Ξ f q n1 m1 ξ1, fun a b => norm_G9_le hf q n1 m1 ξ1 a b, ?_, ?_⟩
  · calc snorm S (a1 + m1 - n1) ≤ snorm S (a1 + m1) + snorm S n1 := snorm_sub_le _ _
      _ ≤ snorm S a1 + snorm S m1 + snorm S n1 := add_le_add (snorm_add_le _ _) le_rfl
      _ ≤ σa + ρ5 + ρ6 := by
          have := snorm_mono hST m1; have := snorm_mono hST n1; linarith
  set eph := 2 * Real.pi * ((N : ℝ) * (Kq * ρ9 * ρ10)) with heph
  have hpt : ∀ n0 n2, regP T ρ9 n2 ≠ 0 →
      ‖∑ m2, (regP T ρ10 m2 : ℂ) * Φ n0 (n1 + (N : ZMod p) * n2) (m1 + (N : ZMod p) * m2)‖ ^ 2 ≤
        ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F9 Ξ f q (a1 + m1 - n1) n0 (n2 - m2) *
          G9 Ξ f q n1 m1 ξ1 n0 m2)‖ ^ 2 + 2 * eph := by
    intro n0 n2 hn2
    have hsn2 : snorm T n2 ≤ ρ9 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ9.le hn2) hρ9.le
    set C := ec (Ξ n1 m1 - ZMod.toAddCircle (ξ1 * m1)) *
      ec ((2 * q) • Ξ n2 m1 + (2 * q ^ 2) • Ξ n2 n2) with hC
    have hCn : ‖C‖ = 1 := by rw [hC, norm_mul, norm_ec, norm_ec, mul_one]
    set H : ZMod p → ℂ := fun m2 =>
      F9 Ξ f q (a1 + m1 - n1) n0 (n2 - m2) * G9 Ξ f q n1 m1 ξ1 n0 m2 with hH
    have hHb : ∀ m2, ‖H m2‖ ≤ 1 := fun m2 => by
      simp only [hH, norm_mul]
      exact mul_le_one₀ (norm_F9_le hf _ _ _ _) (norm_nonneg _) (norm_G9_le hf _ _ _ _ _ _)
    have e1 : ∑ m2, (regP T ρ10 m2 : ℂ) * Φ n0 (n1 + (N : ZMod p) * n2) (m1 + (N : ZMod p) * m2) =
        C * ∑ m2, (regP T ρ10 m2 : ℂ) * (H m2 * ec ((2 * q ^ 2) • (Ξ n2 m2 - Ξ m2 n2))) := by
      rw [mul_sum]
      refine sum_congr rfl fun m2 _ => ?_
      by_cases hm2 : regP T ρ10 m2 = 0
      · simp [hm2]
      · have hsm2 : snorm T m2 ≤ ρ10 :=
          snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ10.le hm2) hρ10.le
        have hs : snorm T n1 + snorm T m1 + (N : ℝ) * (snorm T n2 + snorm T m2) ≤ ρA := by
          have : (N : ℝ) * (snorm T n2 + snorm T m2) ≤ (N : ℝ) * (ρ9 + ρ10) :=
            mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
          linarith
        have := phase9 hΞ1 hΞ2 f hq1 a1 ξ1 n0 n1 m1 n2 m2 hs
        simp only [hΦ]
        rw [this, hC, hH]
        ring
    rw [e1, norm_mul, hCn, one_mul]
    refine (sq_le_sq_add_two_norm (norm_wavg_le_one hP10.1 hP10.2 _ fun m2 => by
      rw [norm_mul, norm_ec, mul_one]; exact hHb m2)
      (norm_wavg_le_one hP10.1 hP10.2 _ hHb)).trans ?_
    have hdiff : ‖∑ m2, (regP T ρ10 m2 : ℂ) * (H m2 * ec ((2 * q ^ 2) • (Ξ n2 m2 - Ξ m2 n2))) -
        ∑ m2, (regP T ρ10 m2 : ℂ) * H m2‖ ≤ eph := by
      rw [← sum_sub_distrib]
      simp_rw [← mul_sub]
      refine norm_wavg_le hP10.1 hP10.2 _ fun m2 hm2 => ?_
      have hsm2 : snorm T m2 ≤ ρ10 :=
        snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ10.le hm2) hρ10.le
      rw [show H m2 * ec ((2 * q ^ 2) • (Ξ n2 m2 - Ξ m2 n2)) - H m2 =
        H m2 * (ec ((2 * q ^ 2) • (Ξ n2 m2 - Ξ m2 n2)) - 1) by ring, norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (hHb m2)).trans ?_
      refine (norm_ec_sub_one_le _).trans ?_
      have e3 : (2 * q ^ 2) • (Ξ n2 m2 - Ξ m2 n2) = N • (q • (Ξ n2 m2 - Ξ m2 n2)) := by
        rw [hNdef, ← mul_nsmul']; congr 1; ring
      rw [e3]
      have h1 : ‖N • (q • (Ξ n2 m2 - Ξ m2 n2))‖ ≤ (N : ℝ) * ‖q • (Ξ n2 m2 - Ξ m2 n2)‖ :=
        norm_nsmul_le
      have h2 := hq n2 m2 hsn2 hsm2
      have h3 : Kq * snorm T n2 * snorm T m2 ≤ Kq * ρ9 * ρ10 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsn2 hKq) hsm2 (snorm_nonneg _)
          (mul_nonneg hKq hρ9.le)
      have h4 : (N : ℝ) * ‖q • (Ξ n2 m2 - Ξ m2 n2)‖ ≤ (N : ℝ) * (Kq * ρ9 * ρ10) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (Nat.cast_nonneg _)
      rw [heph]
      have hpi : 0 < 2 * Real.pi := by positivity
      nlinarith
    linarith
  have hsum : ∑ n0, regP S ρ0 n0 * ∑ n2, regP T ρ9 n2 *
      ‖∑ m2, (regP T ρ10 m2 : ℂ) * Φ n0 (n1 + (N : ZMod p) * n2) (m1 + (N : ZMod p) * m2)‖ ^ 2 ≤
      ∑ n0, regP S ρ0 n0 * ∑ n2, regP T ρ9 n2 *
        ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F9 Ξ f q (a1 + m1 - n1) n0 (n2 - m2) *
          G9 Ξ f q n1 m1 ξ1 n0 m2)‖ ^ 2 + 2 * eph := by
    have : ∀ n0, ∑ n2, regP T ρ9 n2 *
        ‖∑ m2, (regP T ρ10 m2 : ℂ) * Φ n0 (n1 + (N : ZMod p) * n2) (m1 + (N : ZMod p) * m2)‖ ^ 2 ≤
        ∑ n2, regP T ρ9 n2 *
          ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F9 Ξ f q (a1 + m1 - n1) n0 (n2 - m2) *
            G9 Ξ f q n1 m1 ξ1 n0 m2)‖ ^ 2 + 2 * eph := by
      intro n0
      calc _ ≤ ∑ n2, regP T ρ9 n2 *
          (‖∑ m2, (regP T ρ10 m2 : ℂ) * (F9 Ξ f q (a1 + m1 - n1) n0 (n2 - m2) *
            G9 Ξ f q n1 m1 ξ1 n0 m2)‖ ^ 2 + 2 * eph) := by
            refine sum_le_sum fun n2 _ => ?_
            by_cases hn2 : regP T ρ9 n2 = 0
            · simp [hn2]
            · exact mul_le_mul_of_nonneg_left (hpt n0 n2 hn2) (hP9.1 n2)
        _ = _ := by simp only [mul_add, sum_add_distrib, ← sum_mul, hP9.2, one_mul]
    calc _ ≤ ∑ n0, regP S ρ0 n0 * (∑ n2, regP T ρ9 n2 *
          ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F9 Ξ f q (a1 + m1 - n1) n0 (n2 - m2) *
            G9 Ξ f q n1 m1 ξ1 n0 m2)‖ ^ 2 + 2 * eph) :=
          sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left (this n0) (hP0.1 n0)
      _ = _ := by simp only [mul_add, sum_add_distrib, ← sum_mul, hP0.2, one_mul]
  linarith

set_option maxHeartbeats 4000000 in
/-- **Ninth step, second half**: double Cauchy–Schwarz, the local inverse `U²` theorem and the
final change of variables. -/
theorem final9b {S T : Finset (ZMod p)} (hST : S ⊆ T) {ρ0 ρA ρ9 ρ10 σ : ℝ} (hρ0 : 0 < ρ0)
    (hρ10 : 0 < ρ10) {Ξ : ZMod p → ZMod p → UnitAddCircle}
    (hΞ1 : ∀ m, AddOn T ρA (fun n => Ξ n m))
    (hΞ2 : ∀ n, snorm T n ≤ ρA → AddOn T ρA (fun m => Ξ n m))
    (q : ℕ) (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (a2 : ZMod p) (ha2 : snorm S a2 ≤ σ)
    (G : ZMod p → ZMod p → ℂ) (hG : ∀ a b, ‖G a b‖ ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ ∑ n0, regP S ρ0 n0 * ∑ n2, regP T ρ9 n2 *
      ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F9 Ξ f q a2 n0 (n2 - m2) * G n0 m2)‖ ^ 2)
    (h4 : 4 * ρ10 ≤ ρ9) (hsep : 7200 * T.card * ρ10 ≤ (c ^ 2 / 2) ^ 2 * ρ9)
    (hA : 2 * (ρ9 + ρ10) ≤ ρA) (hLQ : 16 * ρ10 ≤ ρA)
    (hsh : 4 * (σ + ((2 * q : ℕ) : ℝ) * ρ9) ≤ ρ0) :
    ∃ (φ : ZMod p → UnitAddCircle) (β : ZMod p → ZMod p),
      LocQuad (sBohr T 0 (2 * ρ10)) φ ∧
      (c ^ 2) ^ 2 / 8 - 50 * S.card * (σ + ((2 * q : ℕ) : ℝ) * ρ9) / ρ0 ≤
        ∑ n, regP S ρ0 n * ‖∑ m, (regP T ρ10 m : ℂ) *
          (f (n + ((2 * q : ℕ) : ZMod p) * m) * ec (-(φ m) - ZMod.toAddCircle (β n * m)))‖ := by
  have hρ9 : 0 < ρ9 := by linarith
  have hP0 := regP_isDist S hρ0.le
  have hP9 := regP_isDist T hρ9.le
  have hP10 := regP_isDist T hρ10.le
  set N : ℕ := 2 * q with hNdef
  have hcs := cs9 hP0.1 hP0.2 hρ9 hρ10 (F9 Ξ f q a2) G (fun a b => norm_F9_le hf q a2 a b) hG
    hc0 hc
  obtain ⟨β, n2, hn2, hpop⟩ := u2pop9 hP0.1 hP0.2 hρ10 h4 (F9 Ξ f q a2)
    (fun a b => norm_F9_le hf q a2 a b) (sq_nonneg c) hsep hcs
  have hsn2 : snorm T n2 ≤ ρ9 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ9.le hn2) hρ9.le
  set L : ZMod p → UnitAddCircle := fun m => Ξ n2 m + Ξ m n2 with hL
  set ψ : ZMod p → UnitAddCircle := fun m => (2 * q ^ 2) • (Ξ m m + L m) with hψ
  set a3 := a2 - (N : ZMod p) * n2 with ha3
  -- unpacking `F₉`
  have hunpack : ∀ n0, ‖∑ m2, (regP T ρ10 m2 : ℂ) * F9 Ξ f q a2 n0 (n2 + m2) *
      ech (-(β n0 * m2))‖ = ‖∑ m2, (regP T ρ10 m2 : ℂ) *
        (f (n0 + a3 - (N : ZMod p) * m2) * ec (-ψ m2) * ech (-(β n0 * m2)))‖ := by
    intro n0
    have e : ∑ m2, (regP T ρ10 m2 : ℂ) * F9 Ξ f q a2 n0 (n2 + m2) * ech (-(β n0 * m2)) =
        ec (-((2 * q ^ 2) • Ξ n2 n2)) * ∑ m2, (regP T ρ10 m2 : ℂ) *
          (f (n0 + a3 - (N : ZMod p) * m2) * ec (-ψ m2) * ech (-(β n0 * m2))) := by
      rw [mul_sum]
      refine sum_congr rfl fun m2 _ => ?_
      by_cases hm2 : regP T ρ10 m2 = 0
      · simp [hm2]
      · have hsm2 : snorm T m2 ≤ ρ10 :=
          snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ10.le hm2) hρ10.le
        have hd := xi_diag_add hΞ1 hΞ2 (y := n2) (h := m2) (by linarith)
        simp only [F9, hψ, hL]
        rw [hd, show n0 + a2 - ((2 * q : ℕ) : ZMod p) * (n2 + m2) =
          n0 + a3 - (N : ZMod p) * m2 by rw [ha3, hNdef]; ring]
        rw [show -((2 * q ^ 2) • (Ξ n2 n2 + (Ξ m2 m2 + (Ξ n2 m2 + Ξ m2 n2)))) =
          -((2 * q ^ 2) • Ξ n2 n2) + -((2 * q ^ 2) • (Ξ m2 m2 + (Ξ n2 m2 + Ξ m2 n2))) by
            rw [nsmul_add]; abel, ec_add]
        ring
    rw [e, norm_mul, norm_ec, one_mul]
  -- the shift `n₀ ↦ n₀ + a₃`
  set g : ZMod p → ℝ := fun x => ‖∑ m2, (regP T ρ10 m2 : ℂ) *
    (f (x - (N : ZMod p) * m2) * ec (-ψ m2) * ech (-(β (x - a3) * m2)))‖ with hg
  have hgb : ∀ x, |g x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (norm_nonneg _)]
    refine norm_wavg_le hP10.1 hP10.2 _ fun m2 _ => ?_
    rw [norm_mul, norm_mul, norm_ec, mul_one, norm_ech, mul_one]; exact hf _
  have hsa3 : snorm S a3 ≤ σ + (N : ℝ) * ρ9 := by
    calc snorm S a3 ≤ snorm S a2 + snorm S ((N : ZMod p) * n2) := snorm_sub_le _ _
      _ ≤ σ + (N : ℝ) * snorm S n2 := add_le_add ha2 (snorm_nsmul_le _ _)
      _ ≤ σ + (N : ℝ) * ρ9 := by
          have := (snorm_mono hST n2).trans hsn2
          nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hshift := shift_real (Γ := S) (Γ' := S) subset_rfl hρ0 hsh hsa3 g hgb
  rw [one_mul] at hshift
  have hga : ∀ n0, g (n0 + a3) = ‖∑ m2, (regP T ρ10 m2 : ℂ) *
      (f (n0 + a3 - (N : ZMod p) * m2) * ec (-ψ m2) * ech (-(β n0 * m2)))‖ := fun n0 => by
    simp only [hg, add_sub_cancel_right]
  have hlow : (c ^ 2) ^ 2 / 8 ≤ ∑ n0, regP S ρ0 n0 * g (n0 + a3) := by
    refine hpop.trans (le_of_eq (sum_congr rfl fun n0 _ => ?_))
    rw [hga, hunpack]
  -- reflection `m ↦ -m`
  refine ⟨fun m => ψ (-m), fun n => -β (n - a3), ?_, ?_⟩
  · have hLadd : AddOn T ρA L := (hΞ2 n2 (by linarith)).add (hΞ1 n2)
    have h1 := lq_diag_lin hΞ1 hΞ2 (r := 2 * ρ10) (by linarith) (by linarith) hLadd
    have h2 := h1.comp (nsmulAddMonoidHom (α := UnitAddCircle) (2 * q ^ 2))
    have h3 := LocQuad.neg_arg (by linarith) h2
    exact h3
  · have hg' : ∀ x, g x = ‖∑ m, (regP T ρ10 m : ℂ) * (f (x + (N : ZMod p) * m) *
        ec (-(ψ (-m)) - ZMod.toAddCircle (-β (x - a3) * m)))‖ := fun x => by
      simp only [hg]
      rw [← sum_regP_neg]
      congr 1
      refine sum_congr rfl fun m _ => ?_
      rw [show x - (N : ZMod p) * -m = x + (N : ZMod p) * m by ring, ech_eq_ec,
        show -(β (x - a3) * -m) = β (x - a3) * m by ring, mul_assoc, ← ec_add]
      congr 2
      rw [neg_mul, map_neg]
      abel
    have := (abs_le.1 hshift).2
    calc (c ^ 2) ^ 2 / 8 - 50 * S.card * (σ + (N : ℝ) * ρ9) / ρ0 ≤
        ∑ n0, regP S ρ0 n0 * g n0 := by
          have e : (50 : ℝ) * S.card * (σ + (N : ℝ) * ρ9) / ρ0 =
              50 * S.card * (σ + (N : ℝ) * ρ9) / ρ0 := rfl
          linarith
      _ = _ := sum_congr rfl fun n0 _ => by rw [hg']

end

end GT
end File_GT_U3S9d

section File_GT_U3S8c
/-!
# Local inverse `U³`, seventh step: the correlation with a locally bilinear phase

Green–Tao, Theorem 9.11: from the correlation estimate of Proposition 9.10 (with the frequency
function `ξ''`) we derive a correlation with the locally bilinear phase `Ξ(n₁, m₁)`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

lemma sq_wavg_swap {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (A B : α → ℂ) (hA : ∀ x, ‖A x‖ ≤ 1) (hB : ∀ x, ‖B x‖ ≤ 1) {ε : ℝ}
    (h : ∀ x, P x ≠ 0 → ‖A x - B x‖ ≤ ε) :
    ‖∑ x, (P x : ℂ) * A x‖ ^ 2 ≤ ‖∑ x, (P x : ℂ) * B x‖ ^ 2 + 2 * ε := by
  have h1 := sq_le_sq_add_two_norm (norm_wavg_le_one hP hP1 A hA) (norm_wavg_le_one hP hP1 B hB)
  have h2 : ‖∑ x, (P x : ℂ) * A x - ∑ x, (P x : ℂ) * B x‖ ≤ ε := by
    rw [← sum_sub_distrib]; simp_rw [← mul_sub]
    exact norm_wavg_le hP hP1 _ h
  linarith

lemma norm_ech_sub_one_le (z : ZMod p) : ‖ech z - 1‖ ≤ 2 * Real.pi * cn z := by
  rw [ech_eq_ec]; exact norm_ec_sub_one_le _

set_option maxHeartbeats 8000000 in
/-- **Seventh step, analytic part** (Green–Tao, Theorem 9.11). -/
theorem step7 {S T : Finset (ZMod p)} (hST : S ⊆ T) {ρ0 ρ4 ρ5 ρ6 r' R B εΞ Qd : ℝ}
    (hρ0 : 0 < ρ0) (hρ4 : 0 < ρ4) (hρ5 : 0 < ρ5) (hρ6 : 0 < ρ6) (hr' : 0 < r')
    (h54 : 4 * ρ5 ≤ ρ4) (h6r : 4 * ρ6 ≤ r') (h40 : 4 * ρ4 ≤ ρ0) (hR : r' + ρ6 ≤ R) (hB : 0 ≤ B)
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (ξ'' : ZMod p → ZMod p)
    (hlin : ∀ x y, snorm T x ≤ R → snorm T y ≤ R → Good T B (ξ'' (x + y) - ξ'' x - ξ'' y))
    (Ξ : ZMod p → ZMod p → UnitAddCircle)
    (hΞ : ∀ n m, snorm T n ≤ ρ6 → snorm T m ≤ ρ5 →
      ‖Ξ n m - ZMod.toAddCircle (ξ'' n * m)‖ ≤ εΞ)
    (a0 ξ0 : ZMod p)
    (hQ : Qd ≤ ∑ n, regP T r' n * ∑ n0, regP S ρ0 n0 *
      ‖∑ m, (regP T ρ4 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
        ech ((ξ'' n - ξ0) * m)‖ ^ 2) :
    ∃ a1 ξ1 : ZMod p, snorm T (a0 - a1) ≤ r' ∧
      Qd - (50 * T.card * ρ6 / r' + 2 * (50 * T.card * ρ5 / ρ4) + 50 * S.card * ρ4 / ρ0 +
          2 * (2 * Real.pi * (B * ρ5)) + 2 * (2 * Real.pi * εΞ)) ≤
        ∑ n0, regP S ρ0 n0 * ∑ n1, regP T ρ6 n1 * ‖∑ m1, (regP T ρ5 m1 : ℂ) *
          (f (n0 + m1 + a1 - n1) * conj (f (n0 + m1)) *
            ec (Ξ n1 m1 - ZMod.toAddCircle (ξ1 * m1)))‖ ^ 2 := by
  have hP0 := regP_isDist S hρ0.le
  have hP4 := regP_isDist T hρ4.le
  have hP5 := regP_isDist T hρ5.le
  have hP6 := regP_isDist T hρ6.le
  have hPr := regP_isDist T hr'.le
  set ea := 50 * T.card * ρ6 / r' with hea
  set eb := 50 * T.card * ρ5 / ρ4 with heb
  set ec' := 50 * S.card * ρ4 / ρ0 with hec
  set ed := 2 * Real.pi * (B * ρ5) with hed
  set ee := 2 * Real.pi * εΞ with hee
  -- the inner averages
  set Ψ : ZMod p → ZMod p → ZMod p → ℂ := fun n0 x h =>
    f (n0 + h + (a0 - x)) * conj (f (n0 + h)) * ech ((ξ'' x - ξ0) * h) with hΨ
  have hΨb : ∀ a b c, ‖Ψ a b c‖ ≤ 1 := fun a b c => by
    simp only [hΨ, norm_mul, norm_ech, mul_one, Complex.norm_conj]
    exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
  set Y : ZMod p → ℝ := fun x => ∑ n0, regP S ρ0 n0 * ‖∑ h, (regP T ρ4 h : ℂ) * Ψ n0 x h‖ ^ 2
    with hY
  have hYb : ∀ x, |Y x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (sum_nonneg fun _ _ => mul_nonneg (hP0.1 _) (sq_nonneg _))]
    calc Y x ≤ ∑ n0, regP S ρ0 n0 * 1 := sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left
          (pow_le_one₀ (norm_nonneg _) (norm_wavg_le_one hP4.1 hP4.2 _ fun _ => hΨb _ _ _))
          (hP0.1 n0)
      _ = 1 := by rw [← sum_mul, hP0.2, one_mul]
  have hQY : Qd ≤ ∑ n, regP T r' n * Y n := by
    refine hQ.trans (le_of_eq (sum_congr rfl fun n _ => ?_))
    simp only [hY, hΨ]
    congr 1; refine sum_congr rfl fun n0 _ => ?_
    congr 3; refine sum_congr rfl fun h _ => ?_
    ring
  -- (a) the shift `n ↦ n + n₁`
  have stepA : ∑ n, regP T r' n * Y n ≤ ∑ n1, regP T ρ6 n1 * ∑ n, regP T r' n * Y (n + n1) + ea := by
    have hpt : ∀ n1, regP T ρ6 n1 ≠ 0 →
        ∑ n, regP T r' n * Y n ≤ ∑ n, regP T r' n * Y (n + n1) + ea := by
      intro n1 hn1
      have hs := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ6.le hn1) hρ6.le
      have := shift_real (Γ := T) (Γ' := T) subset_rfl hr' h6r hs Y hYb
      rw [one_mul] at this
      linarith [(abs_le.1 this).1]
    calc ∑ n, regP T r' n * Y n = ∑ n1, regP T ρ6 n1 * ∑ n, regP T r' n * Y n := by
          rw [← sum_mul, hP6.2, one_mul]
      _ ≤ ∑ n1, regP T ρ6 n1 * (∑ n, regP T r' n * Y (n + n1) + ea) := by
          refine sum_le_sum fun n1 _ => ?_
          by_cases hn1 : regP T ρ6 n1 = 0
          · simp [hn1]
          · exact mul_le_mul_of_nonneg_left (hpt n1 hn1) (hP6.1 n1)
      _ = _ := by simp only [mul_add, sum_add_distrib, ← sum_mul, hP6.2, one_mul]
  -- (b), (c): shifting `h` by `m₁` and merging `n₀ + h`
  set W : ZMod p → ZMod p → ℝ := fun y x => ‖∑ m1, (regP T ρ5 m1 : ℂ) *
    (f (y + m1 + (a0 - x)) * conj (f (y + m1)) * ech ((ξ'' x - ξ0) * m1))‖ with hW
  have hWb : ∀ y x, |W y x ^ 2| ≤ 1 := fun y x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    refine pow_le_one₀ (norm_nonneg _) (norm_wavg_le_one hP5.1 hP5.2 _ fun _ => ?_)
    simp only [norm_mul, norm_ech, mul_one, Complex.norm_conj]
    exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
  have stepB : ∀ n0 x, ‖∑ h, (regP T ρ4 h : ℂ) * Ψ n0 x h‖ ^ 2 ≤
      ∑ h, regP T ρ4 h * W (n0 + h) x ^ 2 + 2 * eb := by
    intro n0 x
    set A' : ℂ := ∑ m1, (regP T ρ5 m1 : ℂ) * ∑ h, (regP T ρ4 h : ℂ) * Ψ n0 x (h + m1) with hA'
    have hdiff : ‖∑ h, (regP T ρ4 h : ℂ) * Ψ n0 x h - A'‖ ≤ eb := by
      rw [norm_sub_rev]
      refine norm_wavg_sub_le hP5.1 hP5.2 _ _ fun m1 hm1 => ?_
      have hs := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ5.le hm1) hρ5.le
      have := regP_shift (Γ := T) (Γ' := T) subset_rfl hρ4 hρ5.le h54
        ((mem_bohr_iff_snorm hρ5.le).2 hs) (fun h => Ψ n0 x h) (fun _ => hΨb _ _ _)
      rw [one_mul] at this
      exact this
    have hA'b : ‖A'‖ ≤ 1 := norm_wavg_le_one hP5.1 hP5.2 _ fun _ =>
      norm_wavg_le_one hP4.1 hP4.2 _ fun _ => hΨb _ _ _
    have h1 := sq_le_sq_add_two_norm
      (norm_wavg_le_one hP4.1 hP4.2 (fun h => Ψ n0 x h) fun _ => hΨb _ _ _) hA'b
    have hswap : A' = ∑ h, (regP T ρ4 h : ℂ) * ∑ m1, (regP T ρ5 m1 : ℂ) * Ψ n0 x (h + m1) := by
      simp only [hA', mul_sum]; rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    have h2 : ‖A'‖ ^ 2 ≤ ∑ h, regP T ρ4 h * ‖∑ m1, (regP T ρ5 m1 : ℂ) * Ψ n0 x (h + m1)‖ ^ 2 := by
      rw [hswap]; exact norm_wsum_sq_le hP4.1 hP4.2 _
    have h3 : ∀ h, ‖∑ m1, (regP T ρ5 m1 : ℂ) * Ψ n0 x (h + m1)‖ = W (n0 + h) x := fun h => by
      have e : ∑ m1, (regP T ρ5 m1 : ℂ) * Ψ n0 x (h + m1) = ech ((ξ'' x - ξ0) * h) *
          ∑ m1, (regP T ρ5 m1 : ℂ) * (f (n0 + h + m1 + (a0 - x)) * conj (f (n0 + h + m1)) *
            ech ((ξ'' x - ξ0) * m1)) := by
        rw [mul_sum]; refine sum_congr rfl fun m1 _ => ?_
        simp only [hΨ]
        rw [mul_add, ech_add, show n0 + (h + m1) = n0 + h + m1 by ring]
        ring
      rw [e, norm_mul, norm_ech, one_mul]
    simp only [h3] at h2
    linarith
  have stepC : ∀ x, Y x ≤ ∑ n0, regP S ρ0 n0 * W n0 x ^ 2 + (2 * eb + ec') := by
    intro x
    have h1 : Y x ≤ ∑ n0, regP S ρ0 n0 * (∑ h, regP T ρ4 h * W (n0 + h) x ^ 2 + 2 * eb) :=
      sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left (stepB n0 x) (hP0.1 n0)
    have h2 : ∑ n0, regP S ρ0 n0 * (∑ h, regP T ρ4 h * W (n0 + h) x ^ 2 + 2 * eb) =
        ∑ h, regP T ρ4 h * ∑ n0, regP S ρ0 n0 * W (n0 + h) x ^ 2 + 2 * eb := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hP0.2, one_mul]
      congr 1
      simp only [mul_sum]; rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    have h3 : ∑ h, regP T ρ4 h * ∑ n0, regP S ρ0 n0 * W (n0 + h) x ^ 2 ≤
        ∑ h, regP T ρ4 h * (∑ n0, regP S ρ0 n0 * W n0 x ^ 2 + ec') := by
      refine sum_le_sum fun h _ => ?_
      by_cases hh : regP T ρ4 h = 0
      · simp [hh]
      · refine mul_le_mul_of_nonneg_left ?_ (hP4.1 h)
        have hs := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ4.le hh) hρ4.le
        have := shift_real (Γ := S) (Γ' := T) hST hρ0 h40 hs (fun y => W y x ^ 2)
          (fun y => hWb y x)
        rw [one_mul] at this
        linarith [(abs_le.1 this).2]
    have h4 : ∑ h, regP T ρ4 h * (∑ n0, regP S ρ0 n0 * W n0 x ^ 2 + ec') =
        ∑ n0, regP S ρ0 n0 * W n0 x ^ 2 + ec' := by
      rw [← sum_mul, hP4.2, one_mul]
    linarith
  -- (d) linearising `ξ''`
  set W2 : ZMod p → ZMod p → ZMod p → ℝ := fun y n n1 => ‖∑ m1, (regP T ρ5 m1 : ℂ) *
    (f (y + m1 + (a0 - n - n1)) * conj (f (y + m1)) *
      ech ((ξ'' n + ξ'' n1 - ξ0) * m1))‖ with hW2
  have stepD : ∀ y n n1, snorm T n ≤ r' → snorm T n1 ≤ ρ6 →
      W y (n + n1) ^ 2 ≤ W2 y n n1 ^ 2 + 2 * ed := by
    intro y n n1 hn hn1
    have hg := hlin n n1 (by linarith) (by linarith)
    simp only [hW, hW2]
    refine sq_wavg_swap hP5.1 hP5.2 _ _ (fun _ => ?_) (fun _ => ?_) fun m1 hm1 => ?_
    · simp only [norm_mul, norm_ech, mul_one, Complex.norm_conj]
      exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
    · simp only [norm_mul, norm_ech, mul_one, Complex.norm_conj]
      exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
    · have hs := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ5.le hm1) hρ5.le
      rw [show a0 - (n + n1) = a0 - n - n1 by ring]
      have e : ech ((ξ'' (n + n1) - ξ0) * m1) = ech ((ξ'' n + ξ'' n1 - ξ0) * m1) *
          ech ((ξ'' (n + n1) - ξ'' n - ξ'' n1) * m1) := by
        rw [← ech_add]; congr 1; ring
      rw [e, show ∀ u v w : ℂ, u * (v * w) - u * v = u * v * (w - 1) by intros; ring,
        norm_mul, norm_mul]
      have hb1 : ‖f (y + m1 + (a0 - n - n1)) * conj (f (y + m1))‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_conj]; exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
      rw [norm_ech, mul_one]
      refine (mul_le_of_le_one_left (norm_nonneg _) hb1).trans ((norm_ech_sub_one_le _).trans ?_)
      rw [hed]
      have := hg m1
      have : B * snorm T m1 ≤ B * ρ5 := mul_le_mul_of_nonneg_left hs hB
      have hpi : 0 < 2 * Real.pi := by positivity
      nlinarith
  -- (e) combine and pigeonhole `n`
  have hmain : Qd - (ea + 2 * eb + ec' + 2 * ed) ≤ ∑ n, regP T r' n *
      ∑ n1, regP T ρ6 n1 * ∑ n0, regP S ρ0 n0 * W2 n0 n n1 ^ 2 := by
    have h1 : ∀ n, regP T r' n ≠ 0 → ∀ n1, regP T ρ6 n1 ≠ 0 →
        Y (n + n1) ≤ ∑ n0, regP S ρ0 n0 * W2 n0 n n1 ^ 2 + (2 * eb + ec' + 2 * ed) := by
      intro n hn n1 hn1
      have hs := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hr'.le hn) hr'.le
      have hs1 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ6.le hn1) hρ6.le
      have h2 : ∑ n0, regP S ρ0 n0 * W n0 (n + n1) ^ 2 ≤
          ∑ n0, regP S ρ0 n0 * (W2 n0 n n1 ^ 2 + 2 * ed) :=
        sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left (stepD n0 n n1 hs hs1) (hP0.1 n0)
      simp only [mul_add, sum_add_distrib, ← sum_mul, hP0.2, one_mul] at h2
      have := stepC (n + n1)
      linarith
    have h2 : ∑ n1, regP T ρ6 n1 * ∑ n, regP T r' n * Y (n + n1) ≤
        ∑ n, regP T r' n * ∑ n1, regP T ρ6 n1 *
          (∑ n0, regP S ρ0 n0 * W2 n0 n n1 ^ 2 + (2 * eb + ec' + 2 * ed)) := by
      have e : ∑ n1, regP T ρ6 n1 * ∑ n, regP T r' n * Y (n + n1) =
          ∑ n, regP T r' n * ∑ n1, regP T ρ6 n1 * Y (n + n1) := by
        simp only [mul_sum]; rw [sum_comm]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      rw [e]
      refine sum_le_sum fun n _ => ?_
      by_cases hn : regP T r' n = 0
      · simp [hn]
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun n1 _ => ?_) (hPr.1 n)
      by_cases hn1 : regP T ρ6 n1 = 0
      · simp [hn1]
      exact mul_le_mul_of_nonneg_left (h1 n hn n1 hn1) (hP6.1 n1)
    have h3 : ∑ n, regP T r' n * ∑ n1, regP T ρ6 n1 *
        (∑ n0, regP S ρ0 n0 * W2 n0 n n1 ^ 2 + (2 * eb + ec' + 2 * ed)) =
        ∑ n, regP T r' n * ∑ n1, regP T ρ6 n1 * ∑ n0, regP S ρ0 n0 * W2 n0 n n1 ^ 2 +
          (2 * eb + ec' + 2 * ed) := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hP6.2, one_mul, hPr.2]
    linarith [hQY, stepA]
  obtain ⟨n, hn, hge⟩ := exists_pos_ge hPr.1 hPr.2 _ hmain
  have hsn := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hr'.le hn) hr'.le
  refine ⟨a0 - n, ξ0 - ξ'' n, by rw [sub_sub_cancel]; exact hsn, ?_⟩
  -- (f), (g): replacing `ξ''(n₁) m₁ / p` by `Ξ(n₁, m₁)`
  have stepG : ∀ n0 n1, regP T ρ6 n1 ≠ 0 → W2 n0 n n1 ^ 2 ≤
      ‖∑ m1, (regP T ρ5 m1 : ℂ) * (f (n0 + m1 + (a0 - n) - n1) * conj (f (n0 + m1)) *
        ec (Ξ n1 m1 - ZMod.toAddCircle ((ξ0 - ξ'' n) * m1)))‖ ^ 2 + 2 * ee := by
    intro n0 n1 hn1
    have hs1 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ6.le hn1) hρ6.le
    simp only [hW2]
    refine sq_wavg_swap hP5.1 hP5.2 _ _ (fun _ => ?_) (fun _ => ?_) fun m1 hm1 => ?_
    · simp only [norm_mul, norm_ech, mul_one, Complex.norm_conj]
      exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
    · simp only [norm_mul, norm_ec, mul_one, Complex.norm_conj]
      exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
    · have hs := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ5.le hm1) hρ5.le
      rw [show n0 + m1 + (a0 - n - n1) = n0 + m1 + (a0 - n) - n1 by ring]
      rw [show ∀ u v w : ℂ, u * v - u * w = u * (v - w) by intros; ring, norm_mul]
      have hb1 : ‖f (n0 + m1 + (a0 - n) - n1) * conj (f (n0 + m1))‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_conj]; exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
      refine (mul_le_of_le_one_left (norm_nonneg _) hb1).trans ?_
      have e : ech ((ξ'' n + ξ'' n1 - ξ0) * m1) =
          ec (ZMod.toAddCircle (ξ'' n1 * m1) - ZMod.toAddCircle ((ξ0 - ξ'' n) * m1)) := by
        rw [ech_eq_ec, ← map_sub]; congr 2; ring
      rw [e]
      refine (norm_ec_sub_ec_le _ _).trans ?_
      rw [hee]
      have := hΞ n1 m1 hs1 hs
      rw [show ZMod.toAddCircle (ξ'' n1 * m1) - ZMod.toAddCircle ((ξ0 - ξ'' n) * m1) -
        (Ξ n1 m1 - ZMod.toAddCircle ((ξ0 - ξ'' n) * m1)) =
        -(Ξ n1 m1 - ZMod.toAddCircle (ξ'' n1 * m1)) by abel, norm_neg]
      have hpi : 0 < 2 * Real.pi := by positivity
      nlinarith
  have hfin : ∑ n1, regP T ρ6 n1 * ∑ n0, regP S ρ0 n0 * W2 n0 n n1 ^ 2 ≤
      ∑ n0, regP S ρ0 n0 * ∑ n1, regP T ρ6 n1 * ‖∑ m1, (regP T ρ5 m1 : ℂ) *
        (f (n0 + m1 + (a0 - n) - n1) * conj (f (n0 + m1)) *
          ec (Ξ n1 m1 - ZMod.toAddCircle ((ξ0 - ξ'' n) * m1)))‖ ^ 2 + 2 * ee := by
    have e : ∑ n1, regP T ρ6 n1 * ∑ n0, regP S ρ0 n0 * W2 n0 n n1 ^ 2 =
        ∑ n0, regP S ρ0 n0 * ∑ n1, regP T ρ6 n1 * W2 n0 n n1 ^ 2 := by
      simp only [mul_sum]; rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [e]
    calc _ ≤ ∑ n0, regP S ρ0 n0 * ∑ n1, regP T ρ6 n1 * (‖∑ m1, (regP T ρ5 m1 : ℂ) *
          (f (n0 + m1 + (a0 - n) - n1) * conj (f (n0 + m1)) *
            ec (Ξ n1 m1 - ZMod.toAddCircle ((ξ0 - ξ'' n) * m1)))‖ ^ 2 + 2 * ee) := by
          refine sum_le_sum fun n0 _ => mul_le_mul_of_nonneg_left
            (sum_le_sum fun n1 _ => ?_) (hP0.1 n0)
          by_cases hn1 : regP T ρ6 n1 = 0
          · simp [hn1]
          · exact mul_le_mul_of_nonneg_left (stepG n0 n1 hn1) (hP6.1 n1)
      _ = _ := by simp only [mul_add, sum_add_distrib, ← sum_mul, hP6.2, one_mul, hP0.2]
  linarith

end

end GT
end File_GT_U3S8c

section File_GT_U3Back
/-!
# Local inverse `U³`: the last three steps combined

From the correlation estimate of Proposition 9.10 (for a frequency function `ξ''` which is
linear on a Bohr set up to a good error) we derive the correlation with a locally quadratic phase,
chaining the seventh, eighth and ninth steps.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

set_option maxHeartbeats 4000000 in
/-- **Steps seven to nine combined.** -/
theorem u3_back (hp : p.Prime) {S T : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) (hST : S ⊆ T)
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (ξ'' : ZMod p → ZMod p) {B Rl : ℝ} (hB : 0 ≤ B)
    (hlin : ∀ x y, snorm T x ≤ Rl → snorm T y ≤ Rl → Good T B (ξ'' (x + y) - ξ'' x - ξ'' y))
    (a0 ξ0 : ZMod p) {σ0 : ℝ} (ha0 : snorm S a0 ≤ σ0)
    {ρ0 r' r3 ρA ρ4 ρ5 ρ6 ρ9 ρ10 c0 : ℝ}
    (hρ0 : 0 < ρ0) (hr' : 0 < r') (hr3 : 0 < r3) (hρA : 0 < ρA) (hρ4 : 0 < ρ4) (hρ5 : 0 < ρ5)
    (hρ6 : 0 < ρ6) (hρ9 : 0 < ρ9) (hρ10 : 0 < ρ10) (hc0 : 0 < c0)
    (hQ : c0 ≤ ∑ n, regP T r' n * ∑ n0, regP S ρ0 n0 *
      ‖∑ m, (regP T ρ4 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
        ech ((ξ'' n - ξ0) * m)‖ ^ 2)
    -- seventh step
    (h54 : 4 * ρ5 ≤ ρ4) (h6r : 4 * ρ6 ≤ r') (h40 : 4 * ρ4 ≤ ρ0) (hR : r' + ρ6 ≤ Rl)
    (hE7 : err7 S T B ρ0 r' r3 ρ4 ρ5 ρ6 ≤ c0 / 2)
    -- the bilinear form
    (hb1 : 4 * (2 ^ (T.card ^ 2) * T.card) * ρA ≤ r3)
    (hb2 : (2 * T.card + 1) * (2 ^ (T.card ^ 2) * T.card) * ρA + r3 ≤ Rl)
    (hb3 : 2 * T.card * (2 ^ (T.card ^ 2) * T.card) * ρA < 1)
    (hb4 : 4 * B * ρA < 1)
    -- eighth step
    (h65 : 8 * ρ6 ≤ ρ5) (h5A : 4 * ρ5 ≤ ρA) (hδ : 100 * T.card * ρ6 / ρ5 ≤ (c0 / 2) ^ 2 / 2)
    (h9R : ρ9 ≤ lqR T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6)
    (h10R : ρ10 ≤ lqR T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6)
    -- ninth step
    (h10 : 4 * ((2 * qbar T c0 ρ5 ρ6) * ρ10) ≤ ρ5) (h9 : 4 * ((2 * qbar T c0 ρ5 ρ6) * ρ9) ≤ ρ6)
    (hA : ρ6 + ρ5 + (2 * qbar T c0 ρ5 ρ6) * (ρ9 + ρ10) ≤ ρA)
    (hE9 : err9 T c0 ρ5 ρ6 ρ9 ρ10 ≤ c0 / 4)
    (h109 : 4 * ρ10 ≤ ρ9) (hsep : 7200 * T.card * ρ10 ≤ ((c0 / 4) ^ 2 / 2) ^ 2 * ρ9)
    (hA' : 2 * (ρ9 + ρ10) ≤ ρA) (hLQ : 16 * ρ10 ≤ ρA)
    (hsh : 4 * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) ≤ ρ0)
    (hfin : 50 * S.card * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) / ρ0 ≤
      ((c0 / 4) ^ 2) ^ 2 / 16) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ qbar T c0 ρ5 ρ6 ∧
      ∃ (φ : ZMod p → UnitAddCircle) (β : ZMod p → ZMod p),
        LocQuad (sBohr T 0 (2 * ρ10)) φ ∧
        c0 ^ 4 / 4096 ≤ ∑ n, regP S ρ0 n * ‖∑ m, (regP T ρ10 m : ℂ) *
          (f (n + ((2 * q : ℕ) : ZMod p) * m) * ec (-(φ m) - ZMod.toAddCircle (β n * m)))‖ := by
  have hT : ∃ s ∈ T, s ≠ 0 := by obtain ⟨s, hs, hs0⟩ := hS; exact ⟨s, hST hs, hs0⟩
  -- the bilinear form
  obtain ⟨Ξ, hΞ1, hΞ2, hΞ3⟩ := bilin7 hp hT hB hr3 hρA hb1 hb2 hb3 hb4 ξ'' hlin
  have hρ5A : ρ5 ≤ ρA := by linarith
  have hρ6A : ρ6 ≤ ρA := by linarith
  have hΞ : ∀ n m, snorm T n ≤ ρ6 → snorm T m ≤ ρ5 →
      ‖Ξ n m - ZMod.toAddCircle (ξ'' n * m)‖ ≤
        B * ρ5 * (50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * ρ6 / r3 + 1) := by
    intro n m hn hm
    refine (hΞ3 n m (hn.trans hρ6A) (hm.trans hρ5A)).trans ?_
    have hK : (0 : ℝ) ≤ 50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) := by positivity
    have h1 : 50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * snorm T n / r3 + 1 ≤
        50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * ρ6 / r3 + 1 := by
      gcongr
    have h0 : 0 ≤ 50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * snorm T n / r3 + 1 := by
      have := snorm_nonneg (S := T) n; positivity
    calc B * snorm T m * (50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * snorm T n / r3
          + 1) ≤ B * ρ5 * (50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * snorm T n / r3
          + 1) := by gcongr
      _ ≤ _ := by gcongr
  -- seventh step
  obtain ⟨a1, ξ1, ha1, hc7⟩ := step7 hST hρ0 hρ4 hρ5 hρ6 hr' h54 h6r h40 hR hB f hf ξ'' hlin Ξ
    hΞ a0 ξ0 hQ
  have hc7' : c0 / 2 ≤ ∑ n0, regP S ρ0 n0 * ∑ n1, regP T ρ6 n1 * ‖∑ m1, (regP T ρ5 m1 : ℂ) *
      (f (n0 + m1 + a1 - n1) * conj (f (n0 + m1)) *
        ec (Ξ n1 m1 - ZMod.toAddCircle (ξ1 * m1)))‖ ^ 2 := by
    unfold err7 at hE7; linarith
  have hsa1 : snorm S a1 ≤ σ0 + r' := by
    have e : a1 = a0 - (a0 - a1) := by ring
    rw [e]
    refine (snorm_sub_le _ _).trans (add_le_add ha0 ?_)
    exact (snorm_mono hST _).trans ha1
  -- eighth step
  have hP0 := regP_isDist S hρ0.le
  obtain ⟨n0, -, hn0⟩ := exists_pos_ge hP0.1 hP0.2 _ hc7'
  set g2 : ZMod p → ℂ := fun u => f (n0 + a1 + u) with hg2
  set g3 : ZMod p → ℂ := fun m => conj (f (n0 + m)) * ec (-ZMod.toAddCircle (ξ1 * m)) with hg3
  have hn0' : c0 / 2 ≤ ∑ n1, regP T ρ6 n1 *
      ‖∑ m1, (regP T ρ5 m1 : ℂ) * (g2 (m1 - n1) * g3 m1 * ec (Ξ n1 m1))‖ ^ 2 := by
    refine hn0.trans (le_of_eq (sum_congr rfl fun n1 _ => ?_))
    congr 3
    refine sum_congr rfl fun m1 _ => ?_
    simp only [hg2, hg3]
    rw [sub_eq_add_neg (Ξ n1 m1), ec_add, show n0 + a1 + (m1 - n1) = n0 + m1 + a1 - n1 by ring]
    ring
  have hδpos : 0 < (c0 / 2) ^ 2 - 100 * T.card * ρ6 / ρ5 := by
    have : 0 < (c0 / 2) ^ 2 := by positivity
    linarith
  obtain ⟨q, hq1, hqb, hq⟩ := sym8 hp hT hρ6 h65 h5A hΞ1 hΞ2 g2 g3
    (fun x => hf _) (fun x => by rw [hg3, norm_mul, norm_ec, mul_one, Complex.norm_conj]; exact hf _)
    (by positivity) hn0' hδpos
  have hqb' : (q : ℝ) ≤ qbar T c0 ρ5 ρ6 := hqb
  have hN : (((2 * q : ℕ) : ℝ)) ≤ 2 * qbar T c0 ρ5 ρ6 := by push_cast; linarith
  have hδ0 : 0 < del8 T c0 ρ5 ρ6 := hδpos
  have hKq : 0 ≤ lqK T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6 := by unfold lqK; positivity
  -- ninth step, first half
  have hq' : ∀ n m, snorm T n ≤ ρ9 → snorm T m ≤ ρ10 →
      ‖q • (Ξ n m - Ξ m n)‖ ≤ lqK T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6 * snorm T n * snorm T m :=
    fun n m hn hm => hq n m (hn.trans h9R) (hm.trans h10R)
  have hN0 : (0 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by positivity
  obtain ⟨a2, G, hG, ha2, hc9⟩ := final9a hST hρ5 hρ6 hρ9 hρ10 hΞ1 hΞ2 hq1 hKq hq' f hf a1 ξ1
    hsa1 hc7' hρ0.le
    (le_trans (by gcongr) h10) (le_trans (by gcongr) h9) (le_trans (by gcongr) hA)
  have hE9' : 2 * (50 * T.card * (((2 * q : ℕ) : ℝ) * ρ10) / ρ5) +
      50 * T.card * (((2 * q : ℕ) : ℝ) * ρ9) / ρ6 +
      2 * (2 * Real.pi * (((2 * q : ℕ) : ℝ) * (lqK T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6 * ρ9 * ρ10)))
      ≤ err9 T c0 ρ5 ρ6 ρ9 ρ10 := by
    unfold err9
    gcongr
  have hc9' : c0 / 4 ≤ ∑ n0, regP S ρ0 n0 * ∑ n2, regP T ρ9 n2 *
      ‖∑ m2, (regP T ρ10 m2 : ℂ) * (F9 Ξ f q a2 n0 (n2 - m2) * G n0 m2)‖ ^ 2 := by
    linarith
  -- ninth step, second half
  obtain ⟨φ, β, hφ, hfin'⟩ := final9b hST hρ0 hρ10 hΞ1 hΞ2 q f hf a2 ha2 G hG (by positivity)
    hc9' h109 hsep hA' hLQ (le_trans (by gcongr) hsh)
  refine ⟨q, hq1, hqb', φ, β, hφ, ?_⟩
  have h50 : 50 * S.card * (σ0 + r' + ρ5 + ρ6 + ((2 * q : ℕ) : ℝ) * ρ9) / ρ0 ≤
      50 * S.card * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) / ρ0 := by
    gcongr
  have e : ((c0 / 4) ^ 2) ^ 2 / 8 - ((c0 / 4) ^ 2) ^ 2 / 16 = c0 ^ 4 / 4096 := by ring
  linarith

end

end GT
end File_GT_U3Back

open Finset KM
open scoped ComplexConjugate
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {S T : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) (hST : S ⊆ T)
    (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (ξ'' : ZMod p → ZMod p) {B Rl : ℝ} (hB : 0 ≤ B)
    (hlin : ∀ x y, snorm T x ≤ Rl → snorm T y ≤ Rl → Good T B (ξ'' (x + y) - ξ'' x - ξ'' y))
    (a0 ξ0 : ZMod p) {σ0 : ℝ} (ha0 : snorm S a0 ≤ σ0)
    {ρ0 r' r3 ρA ρ4 ρ5 ρ6 ρ9 ρ10 c0 : ℝ}
    (hρ0 : 0 < ρ0) (hr' : 0 < r') (hr3 : 0 < r3) (hρA : 0 < ρA) (hρ4 : 0 < ρ4) (hρ5 : 0 < ρ5)
    (hρ6 : 0 < ρ6) (hρ9 : 0 < ρ9) (hρ10 : 0 < ρ10) (hc0 : 0 < c0)
    (hQ : c0 ≤ ∑ n, regP T r' n * ∑ n0, regP S ρ0 n0 *
      ‖∑ m, (regP T ρ4 m : ℂ) * (f (n0 + m + (a0 - n)) * conj (f (n0 + m))) *
        ech ((ξ'' n - ξ0) * m)‖ ^ 2)
    -- seventh step
    (h54 : 4 * ρ5 ≤ ρ4) (h6r : 4 * ρ6 ≤ r') (h40 : 4 * ρ4 ≤ ρ0) (hR : r' + ρ6 ≤ Rl)
    (hE7 : err7 S T B ρ0 r' r3 ρ4 ρ5 ρ6 ≤ c0 / 2)
    -- the bilinear form
    (hb1 : 4 * (2 ^ (T.card ^ 2) * T.card) * ρA ≤ r3)
    (hb2 : (2 * T.card + 1) * (2 ^ (T.card ^ 2) * T.card) * ρA + r3 ≤ Rl)
    (hb3 : 2 * T.card * (2 ^ (T.card ^ 2) * T.card) * ρA < 1)
    (hb4 : 4 * B * ρA < 1)
    -- eighth step
    (h65 : 8 * ρ6 ≤ ρ5) (h5A : 4 * ρ5 ≤ ρA) (hδ : 100 * T.card * ρ6 / ρ5 ≤ (c0 / 2) ^ 2 / 2)
    (h9R : ρ9 ≤ lqR T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6)
    (h10R : ρ10 ≤ lqR T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6)
    -- ninth step
    (h10 : 4 * ((2 * qbar T c0 ρ5 ρ6) * ρ10) ≤ ρ5) (h9 : 4 * ((2 * qbar T c0 ρ5 ρ6) * ρ9) ≤ ρ6)
    (hA : ρ6 + ρ5 + (2 * qbar T c0 ρ5 ρ6) * (ρ9 + ρ10) ≤ ρA)
    (hE9 : err9 T c0 ρ5 ρ6 ρ9 ρ10 ≤ c0 / 4)
    (h109 : 4 * ρ10 ≤ ρ9) (hsep : 7200 * T.card * ρ10 ≤ ((c0 / 4) ^ 2 / 2) ^ 2 * ρ9)
    (hA' : 2 * (ρ9 + ρ10) ≤ ρA) (hLQ : 16 * ρ10 ≤ ρA)
    (hsh : 4 * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) ≤ ρ0)
    (hfin : 50 * S.card * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) / ρ0 ≤
      ((c0 / 4) ^ 2) ^ 2 / 16) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ qbar T c0 ρ5 ρ6 ∧
      ∃ (φ : ZMod p → UnitAddCircle) (β : ZMod p → ZMod p),
        LocQuad (sBohr T 0 (2 * ρ10)) φ ∧
        c0 ^ 4 / 4096 ≤ ∑ n, regP S ρ0 n * ‖∑ m, (regP T ρ10 m : ℂ) *
          (f (n + ((2 * q : ℕ) : ZMod p) * m) * ec (-(φ m) - ZMod.toAddCircle (β n * m)))‖ :=
  @GT.u3_back p _ hp S T hS hST f hf ξ'' B Rl hB hlin a0 ξ0 σ0 ha0 ρ0 r' r3 ρA ρ4 ρ5 ρ6 ρ9 ρ10 c0 hρ0 hr' hr3 hρA hρ4 hρ5 hρ6 hρ9 hρ10 hc0 hQ h54 h6r h40 hR hE7 hb1 hb2 hb3 hb4 h65 h5A hδ h9R h10R h10 h9 hA hE9 h109 hsep hA' hLQ hsh hfin

