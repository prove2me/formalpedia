-- Prove2me | solution 1 for GT.bad_dim_thm
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:52.097198+00:00
-- url     : https://prove2.me/submissions/493d6cea-e1c0-4617-ac72-ee83baa9939f

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_SLA_energy_refined
import Theorems.Thm_GT_label_num
import Theorems.Thm_GT_prop71

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

lemma coe_sum_real {κ : Type*} (s : Finset κ) (f : κ → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : UnitAddCircle) = ∑ i ∈ s, (f i : UnitAddCircle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, AddCircle.coe_add, ih]

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

/-! ### Averages against probability vectors -/

section avg

variable {α : Type*} [Fintype α] {P : α → ℝ}

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

set_option maxHeartbeats 1000000 in
/-- **Mixtures of small translates.** -/
theorem tv_mix {S : Finset (ZMod p)} {n0 : ZMod p} {ρ σ ρq : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hq : 0 ≤ ρq) (h4q : 4 * ρq ≤ σ) (h4σ : 4 * σ ≤ ρ / 2) (Q : ZMod p → ZMod p → ℝ)
    (hQ0 : ∀ a y, 0 ≤ Q a y) (hQ1 : ∀ a, ∑ y, Q a y = 1)
    (hQs : ∀ a y, Q a y ≠ 0 → snorm S y ≤ ρq) (g : ZMod p → ℝ) {B : ℝ}
    (hg : ∀ x, |g x| ≤ B) :
    |∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) -
        ∑ x, regP S (ρ / 2) (x - n0) * g x| ≤
      B * (50 * S.card * ρq / σ) + B * (50 * S.card * σ / (ρ / 2)) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg 0)
  have hP0 : ∀ a, 0 ≤ regP S (ρ / 2) (a - n0) := fun a => regP_nonneg _ _
  have hP1 : ∑ a, regP S (ρ / 2) (a - n0) = 1 := sum_regP_center S (by positivity) n0
  have hU0 : ∀ t, 0 ≤ regP S σ t := fun t => regP_nonneg _ _
  have hU1 : ∑ t, regP S σ t = 1 := sum_regP S hσ.le
  -- step 1: removing `y`
  have step1 : ∀ a, |∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) -
      ∑ t, regP S σ t * g (a + t)| ≤ B * (50 * S.card * ρq / σ) := by
    intro a
    have e1 : ∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) =
        ∑ y, Q a y * ∑ t, regP S σ t * g (a + (t + y)) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun y _ => sum_congr rfl fun t _ => ?_
      rw [add_assoc]; ring
    have e2 : ∑ t, regP S σ t * g (a + t) = ∑ y, Q a y * ∑ t, regP S σ t * g (a + t) := by
      rw [← sum_mul, hQ1, one_mul]
    rw [e1, e2, ← sum_sub_distrib]
    simp_rw [← mul_sub]
    refine abs_wavg_le (hQ0 a) (hQ1 a) _ fun y hy => ?_
    have hyb : y ∈ bohr S ρq := (mem_bohr_iff_snorm hq).mpr (hQs a y hy)
    exact regP_shift_real subset_rfl hσ hq h4q hyb (fun t => g (a + t)) (fun x => hg _)
  -- step 2: removing `t`
  have step2 : |∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t) -
      ∑ x, regP S (ρ / 2) (x - n0) * g x| ≤ B * (50 * S.card * σ / (ρ / 2)) := by
    have e1 : ∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t) =
        ∑ t, regP S σ t * ∑ x, regP S (ρ / 2) x * g (x + t + n0) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun t _ => ?_
      rw [sum_regP_shift_center (S := S) (ρ := ρ / 2) n0
        (fun a w => w * (regP S σ t * g (a + t)))]
      refine sum_congr rfl fun x _ => ?_
      rw [add_right_comm]; ring
    have e2 : ∑ x, regP S (ρ / 2) (x - n0) * g x =
        ∑ t, regP S σ t * ∑ x, regP S (ρ / 2) x * g (x + n0) := by
      rw [← sum_mul, hU1, one_mul]
      exact sum_regP_shift_center (S := S) (ρ := ρ / 2) n0 (fun a w => w * g a)
    rw [e1, e2, ← sum_sub_distrib]
    simp_rw [← mul_sub]
    refine abs_wavg_le hU0 hU1 _ fun t ht => ?_
    have htb : t ∈ bohr S σ := mem_bohr_of_regP_ne_zero hσ.le ht
    have := regP_shift_real subset_rfl (by positivity : (0 : ℝ) < ρ / 2) hσ.le h4σ htb
      (fun x => g (x + n0)) (fun x => hg _)
    refine le_trans (le_of_eq ?_) this
    congr 2
  -- combine
  have hcomb : |∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) -
      ∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t)| ≤
      B * (50 * S.card * ρq / σ) := by
    rw [← sum_sub_distrib]
    simp_rw [← mul_sub]
    exact abs_wavg_le hP0 hP1 _ fun a _ => step1 a
  calc _ = |(∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * ∑ y, Q a y * g (a + t + y) -
        ∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t)) +
        (∑ a, regP S (ρ / 2) (a - n0) * ∑ t, regP S σ t * g (a + t) -
        ∑ x, regP S (ρ / 2) (x - n0) * g x)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hcomb step2)

end

end GT
end File_GT_MixTV

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

namespace DTorus

end DTorus

end

end GT
end File_GT_WeylStep

section File_GT_Subtorus
/-!
# Subtori of lattice tori (replacement for Green–Tao, Theorem 5.1)

For a primitive frequency `k ∈ ℤ^d` of a lattice torus `G`, the subtorus `k^⊥` is again a
lattice torus `G.sub B` (with basis given by an integer matrix `B`), and there is a projection
`π` with `y = ι(π y) + (k·y) u` for a fixed integer vector `u` with `k·u = 1`.
-/

open Finset Matrix

namespace GT

noncomputable section

lemma zmap_apply {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) (x : Fin b → UnitAddCircle) (j : Fin a) :
    zmap M x j = ∑ i, M j i • x i := rfl

lemma zmap_mul {a b c : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) (N : Matrix (Fin b) (Fin c) ℤ)
    (x : Fin c → UnitAddCircle) : zmap (M * N) x = zmap M (zmap N x) := by
  funext j
  simp only [zmap_apply, Matrix.mul_apply, Finset.smul_sum, sum_smul, SemigroupAction.mul_smul]
  exact sum_comm

lemma zmap_one {a : ℕ} (x : Fin a → UnitAddCircle) : zmap (1 : Matrix (Fin a) (Fin a) ℤ) x = x := by
  classical
  funext j
  rw [zmap_apply, sum_eq_single j]
  · simp
  · intro i _ hij; simp [Ne.symm hij]
  · simp

lemma zmap_coe {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) (t : Fin b → ℝ) :
    zmap M (fun i => (t i : UnitAddCircle)) = fun j => ((∑ i, (M j i : ℝ) * t i : ℝ) : UnitAddCircle) := by
  funext j
  rw [zmap_apply, coe_sum_real]
  refine sum_congr rfl fun i _ => ?_
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]

namespace DTorus

lemma sub_emb (G : DTorus) {d' : ℕ} (B : Matrix (Fin d') (Fin G.d) ℤ) (t : Fin d' → ℝ) :
    (G.sub B).emb t = G.emb (fun i => ∑ j, (B j i : ℝ) * t j) := by
  show ∑ i, t i • zmix B G.v i = ∑ i, (∑ j, (B j i : ℝ) * t j) • G.v i
  simp only [zmix, zvec, Finset.smul_sum, smul_smul, sum_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring_nf

lemma exists_lift {d : ℕ} (c : Fin d → UnitAddCircle) :
    ∃ s : Fin d → ℝ, (fun i => (s i : UnitAddCircle)) = c := by
  choose s hs using fun i => QuotientAddGroup.mk_surjective (c i)
  exact ⟨s, funext hs⟩

/-- Restricting a Lipschitz function to a subtorus (and translating) keeps it Lipschitz. -/
lemma isLip_sub {G : DTorus} {F : G.Pt → ℝ} (hF : G.IsLip F) {d' : ℕ}
    (B : Matrix (Fin d') (Fin G.d) ℤ) (c : G.Pt) :
    (G.sub B).IsLip (fun x => F (zmap Bᵀ x + c)) := by
  intro t t'
  obtain ⟨s, rfl⟩ := exists_lift c
  have e : ∀ u : Fin d' → ℝ, zmap Bᵀ ((G.sub B).pt u) + (fun i => (s i : UnitAddCircle)) =
      G.pt (fun i => ∑ j, (B j i : ℝ) * u j + s i) := by
    intro u
    have hu : (G.sub B).pt u = fun j => (u j : UnitAddCircle) := rfl
    rw [hu, zmap_coe]
    funext i
    simp only [pt, Pi.add_apply, AddCircle.coe_add, Matrix.transpose_apply]
  try simp only
  rw [e t, e t']
  refine (hF _ _).trans (le_of_eq ?_)
  rw [sub_emb]
  congr 1
  congr 1
  funext i
  simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]
  ring

end DTorus

lemma Prim.pos_dim {d : ℕ} {k : Fin d → ℤ} (hk : Prim k) : ∃ r, d = r + 1 := by
  cases d with
  | zero => exact absurd (hk 0 (fun j => Fin.elim0 j)) (by simp)
  | succ r => exact ⟨r, rfl⟩

lemma prim_exists_dot_one {r : ℕ} {k : Fin (r + 1) → ℤ} (hk : Prim k) :
    ∃ u0 : Fin (r + 1) → ℤ, ∑ i, k i * u0 i = 1 := by
  obtain ⟨V, -, hV⟩ := exists_unimod_reduce _ k rfl hk
  refine ⟨fun i => V i 0, ?_⟩
  have := congrFun hV 0
  simpa [Matrix.vecMul, dotProduct] using this

/-- **Bounded Bézout**: a primitive integer vector `k` admits `u` with `k·u = 1` and
`|u_i| ≤ 1 + ∑ |k_j|`. -/
lemma exists_bezout_bounded {d : ℕ} {k : Fin d → ℤ} (hk : Prim k) :
    ∃ u : Fin d → ℤ, ∑ i, k i * u i = 1 ∧ ∀ i, |u i| ≤ 1 + ∑ j, |k j| := by
  classical
  obtain ⟨r, rfl⟩ := hk.pos_dim
  obtain ⟨u0, hu0⟩ := prim_exists_dot_one hk
  obtain ⟨i0, hi0⟩ : ∃ i0, k i0 ≠ 0 := by
    by_contra h; push_neg at h; simp [h] at hu0
  set a := k i0 with ha
  set rr : Fin (r + 1) → ℤ := fun l => u0 l % a with hrr
  set X : ℤ := u0 i0 + ∑ l ∈ univ.erase i0, k l * (u0 l / a) with hX
  have hsplit : ∀ f : Fin (r + 1) → ℤ, ∑ l, f l = f i0 + ∑ l ∈ univ.erase i0, f l := fun f =>
    (add_sum_erase _ _ (mem_univ i0)).symm
  have hdot : a * X + ∑ l ∈ univ.erase i0, k l * rr l = 1 := by
    rw [← hu0, hsplit (fun l => k l * u0 l), hX, mul_add, mul_sum, add_assoc, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun l _ => ?_
    have := Int.emod_add_mul_ediv (u0 l) a
    simp only [hrr]
    linear_combination (k l) * this
  have hSk : |a| ≤ ∑ j, |k j| := single_le_sum (f := fun j => |k j|) (fun j _ => abs_nonneg _)
    (mem_univ i0)
  have ha1 : 1 ≤ |a| := Int.one_le_abs hi0
  have hrr0 : ∀ l, 0 ≤ rr l ∧ rr l < |a| := fun l =>
    ⟨Int.emod_nonneg _ hi0, by have := Int.emod_lt (u0 l) hi0; rwa [Int.natCast_natAbs] at this⟩
  refine ⟨fun l => if l = i0 then X else rr l, ?_, fun i => ?_⟩
  · rw [hsplit]
    simp only [ite_true]
    rw [← hdot, ← ha]
    congr 1
    refine sum_congr rfl fun l hl => ?_
    rw [if_neg (ne_of_mem_erase hl)]
  · by_cases hi : i = i0
    · show |if i = i0 then X else rr i| ≤ _
      rw [if_pos hi]
      set S' := ∑ l ∈ univ.erase i0, |k l| with hS'
      have hS'le : S' + |a| ≤ ∑ j, |k j| := by
        rw [hsplit (fun j => |k j|)]; linarith [abs_nonneg a]
      have hS'0 : 0 ≤ S' := sum_nonneg fun l _ => abs_nonneg _
      have hbound : |∑ l ∈ univ.erase i0, k l * rr l| ≤ |a| * S' := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        rw [hS', mul_sum]
        refine sum_le_sum fun l _ => ?_
        rw [abs_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [abs_of_nonneg (hrr0 l).1]; exact (hrr0 l).2.le
      have haX : |a| * |X| ≤ 1 + |a| * S' := by
        rw [← abs_mul]
        have : a * X = 1 - ∑ l ∈ univ.erase i0, k l * rr l := by linarith
        rw [this]
        refine (abs_sub _ _).trans ?_
        simp only [abs_one]; linarith
      by_contra hcon
      push_neg at hcon
      have : S' + 2 ≤ |X| := by linarith
      nlinarith
    · show |if i = i0 then X else rr i| ≤ _
      rw [if_neg hi, abs_of_nonneg (hrr0 i).1]
      linarith [(hrr0 i).2]

section lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram determinant of the sublattice `k^⊥` (spanned by the columns `1, …, r` of a
unimodular `W` with `k W = e₀`) is at most `2^{d²} K² det Gram(v)`, `K = ∑ |k_i| / ‖v_i‖`. -/
lemma gdet_sub_le {r : ℕ} {v : Fin (r + 1) → E} (hv : LinearIndependent ℝ v)
    (hred : (∏ i, ‖v i‖) ^ 2 ≤ 2 ^ ((r + 1) ^ 2) * gdet v)
    {k : Fin (r + 1) → ℤ} {W : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ} (hW : IsUnit W.det)
    (hkW : k ᵥ* W = Pi.single 0 1) :
    0 < gdet (zmix (Matrix.of fun (j : Fin r) (i : Fin (r + 1)) => W i j.succ) v) ∧
      gdet (zmix (Matrix.of fun (j : Fin r) (i : Fin (r + 1)) => W i j.succ) v) ≤
        2 ^ ((r + 1) ^ 2) * (∑ i, |(k i : ℝ)| / ‖v i‖) ^ 2 * gdet v := by
  set B0 : Matrix (Fin r) (Fin (r + 1)) ℤ := Matrix.of fun j i => W i j.succ with hB0
  set w := zmix B0 v with hw
  set x : E := zvec (fun i => W i 0) v with hxdef
  have hcons : zmix Wᵀ v = Fin.cons x w := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero]; rfl
    · simp only [Fin.cons_succ]; rfl
  have hg : gdet (Fin.cons x w : Fin (r + 1) → E) = gdet v := by
    rw [← hcons, gdet_zmix_unimod (by rwa [Matrix.det_transpose]) v]
  obtain ⟨y, hy, c, hx⟩ := exists_orth_decomp x w
  have hgy : gdet v = ‖y‖ ^ 2 * gdet w := by rw [← hg, gdet_cons_eq hy hx]
  have hg0 : 0 < gdet v := gdet_pos hv
  set t : Fin (r + 1) → ℝ := fun i => (W i 0 : ℝ) - ∑ j, c j * W i j.succ with ht
  have hyt : y = ∑ i, t i • v i := by
    have e1 : y = x - ∑ j, c j • w j := by rw [hx]; abel
    rw [e1, hxdef, hw]
    simp only [zmix, zvec, ht, sub_smul, sum_sub_distrib, Finset.smul_sum, smul_smul, sum_smul,
      hB0, Matrix.of_apply]
    congr 1
    rw [sum_comm]
  have hkt : ∑ i, (k i : ℝ) * t i = 1 := by
    have h0 : ∑ i, k i * W i 0 = 1 := by
      have := congrFun hkW 0
      simpa [Matrix.vecMul, dotProduct] using this
    have hs : ∀ j : Fin r, ∑ i, k i * W i j.succ = 0 := by
      intro j
      have := congrFun hkW j.succ
      simpa [Matrix.vecMul, dotProduct, Pi.single_apply, Fin.succ_ne_zero] using this
    have h0' : ∑ i, (k i : ℝ) * W i 0 = 1 := by exact_mod_cast h0
    have hs' : ∀ j : Fin r, ∑ i, (k i : ℝ) * W i j.succ = 0 := fun j => by exact_mod_cast hs j
    simp only [ht, mul_sub, sum_sub_distrib, h0', mul_sum]
    rw [sum_comm]
    have : ∑ j : Fin r, ∑ i, (k i : ℝ) * (c j * W i j.succ) = 0 := by
      refine sum_eq_zero fun j _ => ?_
      rw [show ∑ i, (k i : ℝ) * (c j * W i j.succ) = c j * ∑ i, (k i : ℝ) * W i j.succ by
        rw [mul_sum]; exact sum_congr rfl fun i _ => by ring, hs' j, mul_zero]
    rw [this, sub_zero]
  have hvpos : ∀ i, 0 < ‖v i‖ := fun i => norm_pos_iff.mpr (hv.ne_zero i)
  set P := ∏ i, ‖v i‖ with hP
  have hP0 : 0 < P := prod_pos fun i _ => hvpos i
  have hsg : 0 < Real.sqrt (gdet v) := Real.sqrt_pos.mpr hg0
  have hti : ∀ i, |t i| ≤ ‖y‖ * P / (Real.sqrt (gdet v) * ‖v i‖) := by
    intro i
    have := coord_bound v t i
    rw [← hyt] at this
    rw [le_div_iff₀ (mul_pos hsg (hvpos i))]
    linarith
  set K := ∑ i, |(k i : ℝ)| / ‖v i‖ with hK
  have h1 : 1 ≤ ‖y‖ * (P / Real.sqrt (gdet v)) * K := by
    calc (1 : ℝ) = ∑ i, (k i : ℝ) * t i := hkt.symm
      _ ≤ ∑ i, |(k i : ℝ)| * |t i| := by
          refine (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (le_of_eq ?_))
          exact sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i, |(k i : ℝ)| * (‖y‖ * P / (Real.sqrt (gdet v) * ‖v i‖)) :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hti i) (abs_nonneg _)
      _ = ‖y‖ * (P / Real.sqrt (gdet v)) * K := by
          rw [hK, mul_sum]
          refine sum_congr rfl fun i _ => ?_
          field_simp
  have hK0 : 0 ≤ K := sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (hvpos i).le
  have h2 : 1 ≤ ‖y‖ ^ 2 * (2 ^ ((r + 1) ^ 2) * K ^ 2) := by
    have h1' : (1 : ℝ) ≤ (‖y‖ * (P / Real.sqrt (gdet v)) * K) ^ 2 := by nlinarith
    have hq : (P / Real.sqrt (gdet v)) ^ 2 ≤ 2 ^ ((r + 1) ^ 2) := by
      rw [div_pow, Real.sq_sqrt hg0.le, div_le_iff₀ hg0]
      exact hred
    calc (1 : ℝ) ≤ (‖y‖ * (P / Real.sqrt (gdet v)) * K) ^ 2 := h1'
      _ = ‖y‖ ^ 2 * (P / Real.sqrt (gdet v)) ^ 2 * K ^ 2 := by ring
      _ ≤ ‖y‖ ^ 2 * 2 ^ ((r + 1) ^ 2) * K ^ 2 := by gcongr
      _ = _ := by ring
  have hy0 : 0 < ‖y‖ ^ 2 := by
    rcases (sq_nonneg ‖y‖).lt_or_eq with h | h
    · exact h
    · rw [← h] at h2; simp at h2; linarith
  have hw0 : 0 < gdet w := by
    have := gdet_nonneg w
    rcases this.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hgy; linarith
  refine ⟨hw0, ?_⟩
  have : gdet w * 1 ≤ gdet w * (‖y‖ ^ 2 * (2 ^ ((r + 1) ^ 2) * K ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 hw0.le
  calc gdet w = gdet w * 1 := (mul_one _).symm
    _ ≤ gdet w * (‖y‖ ^ 2 * (2 ^ ((r + 1) ^ 2) * K ^ 2)) := this
    _ = 2 ^ ((r + 1) ^ 2) * K ^ 2 * (‖y‖ ^ 2 * gdet w) := by ring
    _ = _ := by rw [← hgy]

end lattice

lemma kdot_smul_vec {d : ℕ} {k u : Fin d → ℤ} (hu : ∑ i, k i * u i = 1) (t : UnitAddCircle) :
    kdot k (fun i => u i • t) = t := by
  rw [kdot_apply]
  simp only [← SemigroupAction.mul_smul, ← sum_smul, hu, one_smul]

/-- The torus decomposition `y = ι(π₀ y) + (k·y) u` attached to a unimodular `W` with `k W = e₀`
and an integer vector `u` with `k·u = 1`. -/
lemma torus_decomp {r : ℕ} {k : Fin (r + 1) → ℤ} {W : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ}
    (hW : IsUnit W.det) (hkW : k ᵥ* W = Pi.single 0 1) {u : Fin (r + 1) → ℤ}
    (hu : ∑ i, k i * u i = 1) :
    ∃ π0 : (Fin (r + 1) → UnitAddCircle) →+ (Fin r → UnitAddCircle), ∀ y,
      y = zmap (Matrix.of fun (j : Fin r) (i : Fin (r + 1)) => W i j.succ)ᵀ (π0 y) +
        fun i => u i • kdot k y := by
  have hWW : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hW
  have hrow : ∀ i, W⁻¹ 0 i = k i := by
    intro i
    have h1 : k ᵥ* W ᵥ* W⁻¹ = k := by rw [Matrix.vecMul_vecMul, hWW, Matrix.vecMul_one]
    rw [hkW, Matrix.single_one_vecMul] at h1
    exact congrFun h1 i
  set L : (Fin (r + 1) → UnitAddCircle) →+ (Fin (r + 1) → UnitAddCircle) :=
    AddMonoidHom.mk' (fun y => y - fun i => u i • kdot k y) (by
      intro a b; funext i; simp only [map_add, smul_add, Pi.sub_apply, Pi.add_apply]; abel)
    with hL
  refine ⟨AddMonoidHom.mk' (fun y j => zmap W⁻¹ (L y) j.succ) (by
    intro a b; funext j; simp only [map_add, Pi.add_apply]), fun y => ?_⟩
  set z := L y with hz
  have hkz : kdot k z = 0 := by
    rw [hz, hL, AddMonoidHom.mk'_apply, map_sub, kdot_smul_vec hu, sub_self]
  set c := zmap W⁻¹ z with hc
  have hc0 : c 0 = 0 := by
    rw [hc, zmap_apply, ← hkz, kdot_apply]
    exact sum_congr rfl fun i _ => by rw [hrow]
  have hWc : zmap W c = z := by rw [hc, ← zmap_mul, hWW, zmap_one]
  have hzeq : z = zmap (Matrix.of fun (j : Fin r) (i : Fin (r + 1)) => W i j.succ)ᵀ
      (fun j : Fin r => c j.succ) := by
    rw [← hWc]
    funext i
    rw [zmap_apply, zmap_apply, Fin.sum_univ_succ, hc0, smul_zero, zero_add]
    rfl
  have : (AddMonoidHom.mk' (fun y j => zmap W⁻¹ (L y) j.succ) (by
      intro a b; funext j; simp only [map_add, Pi.add_apply])) y = fun j : Fin r => c j.succ := rfl
  rw [this, ← hzeq, hz, hL, AddMonoidHom.mk'_apply, sub_add_cancel]

/-- **Subtori.** For a primitive frequency `k` of a good lattice torus `G`, the subtorus `k^⊥`
is a good lattice torus `G.sub B` of dimension `d - 1` and volume at most
`2^{d²} (∑ |k_i|/‖v_i‖) vol(G)`, with a projection `π` such that `y = ι(π y) + (k·y) u`,
where `ι = zmap Bᵀ` and `u` is an integer vector with `|u_i| ≤ 1 + ∑|k_j|`. -/
theorem subtorus {G : DTorus} (hG : G.Good) {k : Fin G.d → ℤ} (hk : Prim k) :
    ∃ (d' : ℕ) (B : Matrix (Fin d') (Fin G.d) ℤ)
      (π : (Fin G.d → UnitAddCircle) →+ (Fin d' → UnitAddCircle)) (u : Fin G.d → ℤ),
      d' + 1 = G.d ∧ (G.sub B).Good ∧
      (G.sub B).vol ≤ 2 ^ (G.d ^ 2) * (∑ i, |(k i : ℝ)| / ‖G.v i‖) * G.vol ∧
      (∀ i, |u i| ≤ 1 + ∑ j, |k j|) ∧
      ∀ y, y = zmap Bᵀ (π y) + fun i => u i • kdot k y := by
  obtain ⟨d, n, v⟩ := G
  obtain ⟨r, rfl⟩ := hk.pos_dim
  obtain ⟨hv, hmin, hred⟩ := hG
  (try simp only at hv hmin hred k hk ⊢)
  obtain ⟨u, hu, hub⟩ := exists_bezout_bounded hk
  obtain ⟨W, hW, hkW⟩ := exists_unimod_reduce _ k rfl hk
  obtain ⟨π0, hπ0⟩ := torus_decomp hW hkW hu
  set B0 : Matrix (Fin r) (Fin (r + 1)) ℤ := Matrix.of fun j i => W i j.succ with hB0
  obtain ⟨hw0, hwle⟩ := gdet_sub_le hv hred hW hkW
  rw [← hB0] at hw0 hwle
  have hwind : LinearIndependent ℝ (zmix B0 v) := linearIndependent_of_gdet_ne_zero hw0.ne'
  obtain ⟨M, hM, hMred⟩ := hermite r (zmix B0 v) hwind
  have hMT : IsUnit (Mᵀ).det := by rwa [Matrix.det_transpose]
  set B := M * B0 with hB
  have hsubv : (DTorus.sub ⟨r + 1, n, v⟩ B).v = zmix M (zmix B0 v) := by
    rw [zmix_zmix] <;> rfl
  have hgM : gdet (zmix M (zmix B0 v)) = gdet (zmix B0 v) := gdet_zmix_unimod hM _
  refine ⟨r, B, (zmap (Mᵀ)⁻¹).comp π0, u, rfl, ⟨?_, ?_, ?_⟩, ?_, hub, ?_⟩
  · rw [hsubv]; exact linIndep_zmix_unimod hM hwind
  · intro m hm
    rw [DTorus.sub_emb]
    have hmB : m ᵥ* B ≠ 0 := by
      intro h0
      have hm' : m ᵥ* M ≠ 0 := by
        intro h1
        apply hm
        have : m ᵥ* M ᵥ* M⁻¹ = m := by
          rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hM, Matrix.vecMul_one]
        rw [← this, h1, Matrix.zero_vecMul]
      apply hm'
      set m' := m ᵥ* M
      have h2 : W *ᵥ (Fin.cons 0 m' : Fin (r + 1) → ℤ) = 0 := by
        rw [hB, ← Matrix.vecMul_vecMul] at h0
        funext i
        have := congrFun h0 i
        simp only [Matrix.vecMul, dotProduct, hB0, Matrix.of_apply, Pi.zero_apply] at this
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, mul_zero,
          zero_add, Fin.cons_succ, Pi.zero_apply]
        rw [← this]
        exact sum_congr rfl fun j _ => mul_comm _ _
      have h3 : (Fin.cons 0 m' : Fin (r + 1) → ℤ) = 0 := by
        have : W⁻¹ *ᵥ (W *ᵥ (Fin.cons 0 m' : Fin (r + 1) → ℤ)) = Fin.cons 0 m' := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul W hW, Matrix.one_mulVec]
        rw [← this, h2, Matrix.mulVec_zero]
      funext j
      have := congrFun h3 j.succ
      simpa using this
    have h1 := hmin (m ᵥ* B) hmB
    refine le_trans h1 (le_of_eq ?_)
    congr 2
    funext i
    simp only [Matrix.vecMul, dotProduct]
    push_cast
    exact sum_congr rfl fun j _ => mul_comm _ _
  · change (∏ i, ‖(DTorus.sub ⟨r + 1, n, v⟩ B).v i‖) ^ 2 ≤ 2 ^ (r ^ 2) * gdet (DTorus.sub ⟨r + 1, n, v⟩ B).v
    rw [hsubv, hgM]
    exact hMred
  · change ∏ i, ‖(DTorus.sub ⟨r + 1, n, v⟩ B).v i‖ ≤ 2 ^ ((r + 1) ^ 2) *
      (∑ i, |(k i : ℝ)| / ‖v i‖) * ∏ i, ‖v i‖
    rw [hsubv]
    set K := ∑ i, |(k i : ℝ)| / ‖v i‖
    have hK0 : 0 ≤ K := sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (norm_nonneg _)
    have hP0 : 0 ≤ ∏ i, ‖v i‖ := prod_nonneg fun i _ => norm_nonneg _
    have hgv : gdet v ≤ (∏ i, ‖v i‖) ^ 2 := by rw [← prod_pow]; exact gdet_le_prod v
    have hpow : (2 : ℝ) ^ (r ^ 2) ≤ 2 ^ ((r + 1) ^ 2) :=
      pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left (Nat.le_succ r) 2)
    rw [← sq_le_sq₀ (prod_nonneg fun i _ => norm_nonneg _) (by positivity)]
    calc (∏ i, ‖zmix M (zmix B0 v) i‖) ^ 2 ≤ 2 ^ (r ^ 2) * gdet (zmix B0 v) := hMred
      _ ≤ 2 ^ (r ^ 2) * (2 ^ ((r + 1) ^ 2) * K ^ 2 * gdet v) :=
          mul_le_mul_of_nonneg_left hwle (by positivity)
      _ ≤ 2 ^ ((r + 1) ^ 2) * (2 ^ ((r + 1) ^ 2) * K ^ 2 * (∏ i, ‖v i‖) ^ 2) := by
          have := gdet_nonneg v
          gcongr
      _ = (2 ^ ((r + 1) ^ 2) * K * ∏ i, ‖v i‖) ^ 2 := by ring
  · intro y
    rw [AddMonoidHom.comp_apply, hB, Matrix.transpose_mul, zmap_mul, ← zmap_mul Mᵀ,
      Matrix.mul_nonsing_inv _ hMT, zmap_one]
    exact hπ0 y

/-- Moving a point of the torus by `t·u` (`u` an integer vector) changes a Lipschitz function by
at most `‖t‖ ‖∑ u_i v_i‖`. -/
lemma DTorus.IsLip.shift {G : DTorus} {F : G.Pt → ℝ} (hF : G.IsLip F) (x : G.Pt)
    (u : Fin G.d → ℤ) (t : UnitAddCircle) :
    |F x - F (x - fun i => u i • t)| ≤ ‖t‖ * ‖G.emb (fun i => (u i : ℝ))‖ := by
  obtain ⟨s, rfl⟩ := DTorus.exists_lift x
  obtain ⟨θ, rfl, hθ, -⟩ := exists_rep t
  have e : ((fun i => (s i : UnitAddCircle)) - fun i => u i • (θ : UnitAddCircle)) =
      G.pt (fun i => s i - θ * u i) := by
    funext i
    simp only [DTorus.pt, Pi.sub_apply, AddCircle.coe_sub]
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm]
  have hs : (fun i => (s i : UnitAddCircle)) = G.pt s := rfl
  rw [e, hs]
  refine (hF _ _).trans (le_of_eq ?_)
  have : s - (fun i => s i - θ * u i) = θ • fun i => (u i : ℝ) := by
    funext i; simp [Pi.smul_apply]
  rw [this, hθ.symm]
  unfold DTorus.emb
  rw [← Real.norm_eq_abs, ← norm_smul, Finset.smul_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_smul]

end

end GT
end File_GT_Subtorus

section File_GT_Refine
/-!
# Refining a poorly distributed label

Combining Proposition 7.1 with the subtorus construction: a poorly distributed label admits a
codimension-one subtorus such that, near every base point, `F ∘ Ξ` is approximated by a function
on the subtorus.
-/

open Finset KM Matrix

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

set_option maxHeartbeats 1000000 in
/-- **Refinement of a poor label.** -/
theorem poor_refine (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) {n0 : ZMod p}
    {ρ : ℝ} (hρ : 0 < ρ) {ε4 : ℝ} (hε0 : 0 < ε4) (hε8 : ε4 ≤ 1 / 8)
    {G : DTorus} (hG : G.Good) {F : G.Pt → ℝ} (hF : G.IsLip F) (hF1 : ∀ x, |F x| ≤ 1)
    {Ξ : ZMod p → G.Pt} (hL : LocQuad (sBohr S n0 ρ) Ξ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsmall : 100 * S.card * ε4 ≤ wδ G η / 2)
    (hpoor : ∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        (F (Ξ z.1) * F (Ξ (z.1 + z.2)) * F (Ξ (z.1 + 2 * z.2)) * F (Ξ (z.1 + 3 * z.2))) <
      (∑ z : ZMod p × ZMod p, regP S (ρ / 2) (z.1 - n0) * regP S (ε4 * ρ) z.2 *
        F (Ξ z.1)) ^ 4 - η / 2) :
    ∃ (m : ℕ) (ξ : ZMod p → ZMod p) (d' : ℕ) (B : Matrix (Fin d') (Fin G.d) ℤ)
      (π : (Fin G.d → UnitAddCircle) →+ (Fin d' → UnitAddCircle)) (u : Fin G.d → ℤ),
      1 ≤ m ∧ (m : ℝ) ≤ p71m S G η ∧ d' + 1 = G.d ∧ (G.sub B).Good ∧
      (G.sub B).vol ≤ 2 ^ (G.d ^ 2) * (∑ i, 4 * (wM G η i : ℝ) / ‖G.v i‖) * G.vol ∧
      (∀ i, |(u i : ℝ)| ≤ 1 + ∑ j, 4 * (wM G η j : ℝ)) ∧
      ∀ a, snorm S (a - n0) ≤ ρ / 2 → ∀ b h : ZMod p,
        snorm S (b - a) ≤ p71R S G η ε4 ρ →
        snorm (insert (ξ a) S) h ≤ p71R S G η ε4 ρ → 8 * m * snorm (insert (ξ a) S) h ≤ ρ →
        |F (Ξ (b + ((2 * m : ℕ) : ZMod p) * h)) -
          F (zmap Bᵀ (π (Ξ (b + ((2 * m : ℕ) : ZMod p) * h) - Ξ b)) + Ξ b)| ≤
          p71L S G η ε4 ρ m * snorm (insert (ξ a) S) h * ‖G.emb (fun i => (u i : ℝ))‖ := by
  classical
  obtain ⟨k, hk, hkb, m, hm1, hmb, hlin⟩ :=
    prop71 hp hS hρ hε0 hε8 hG hF hF1 hL hη hη1 hsmall hpoor
  have hξ : ∀ a, ∃ ξ : ZMod p, snorm S (a - n0) ≤ ρ / 2 → ∀ b h : ZMod p,
      snorm S (b - a) ≤ p71R S G η ε4 ρ →
      snorm (insert ξ S) h ≤ p71R S G η ε4 ρ → 8 * m * snorm (insert ξ S) h ≤ ρ →
      ‖kdot k (Ξ (b + ((2 * m : ℕ) : ZMod p) * h) - Ξ b)‖ ≤
        p71L S G η ε4 ρ m * snorm (insert ξ S) h := by
    intro a
    by_cases ha : snorm S (a - n0) ≤ ρ / 2
    · obtain ⟨ξ, hξ⟩ := hlin a ha
      exact ⟨ξ, fun _ => hξ⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose ξ hξ using hξ
  obtain ⟨d', B, π, u, hd', hGood, hvol, hu, hdec⟩ := subtorus hG hk
  have hkb' : ∀ i, |(k i : ℝ)| ≤ 4 * (wM G η i : ℝ) := by
    intro i
    have := hkb i
    have : ((|k i| : ℤ) : ℝ) ≤ ((4 * (wM G η i : ℤ) : ℤ) : ℝ) := by exact_mod_cast this.le
    push_cast at this; exact this
  refine ⟨m, ξ, d', B, π, u, hm1, hmb, hd', hGood, ?_, ?_, ?_⟩
  · refine hvol.trans ?_
    have hvol0 : 0 ≤ G.vol := by unfold DTorus.vol; exact prod_nonneg fun i _ => norm_nonneg _
    gcongr with i
    exact hkb' i
  · intro i
    have h1 : ((|u i| : ℤ) : ℝ) ≤ ((1 + ∑ j, |k j| : ℤ) : ℝ) := by exact_mod_cast hu i
    push_cast at h1
    refine h1.trans ?_
    gcongr with j
    exact hkb' j
  · intro a ha b h hb hh hhρ
    set x := Ξ (b + ((2 * m : ℕ) : ZMod p) * h) with hx
    have e : zmap Bᵀ (π (x - Ξ b)) + Ξ b = x - fun i => u i • kdot k (x - Ξ b) := by
      have := hdec (x - Ξ b)
      rw [eq_sub_iff_add_eq, add_right_comm, ← this, sub_add_cancel]
    rw [e]
    refine (DTorus.IsLip.shift hF x u (kdot k (x - Ξ b))).trans ?_
    exact mul_le_mul_of_nonneg_right (hξ a ha b h hb hh hhρ) (norm_nonneg _)

end

end GT
end File_GT_Refine

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

end SLA

/-! ### Locally quadratic maps -/

lemma LocQuad.mono {B B' : Set (ZMod p)} {M : Type*} [AddCommGroup M] {Ξ : ZMod p → M}
    (hL : LocQuad B Ξ) (hB : B' ⊆ B) : LocQuad B' Ξ := by
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  exact hL n h1 h2 h3 (hB m0) (hB m1) (hB m2) (hB m3) (hB m12) (hB m13) (hB m23) (hB m123)

lemma LocQuad.sub_const {B : Set (ZMod p)} {M : Type*} [AddCommGroup M] {Ξ : ZMod p → M}
    (hL : LocQuad B Ξ) (c : M) : LocQuad B (fun x => Ξ x - c) := by
  intro n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  have := hL n h1 h2 h3 m0 m1 m2 m3 m12 m13 m23 m123
  beta_reduce
  refine Eq.trans ?_ this
  abel

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

lemma ldata_OK {v : SLA p} (hv : v.Valid) (c : v.C) : (v.ldata c).OK :=
  ⟨hv.2.2.1 c, hv.2.2.2.1 c, hv.2.2.2.2.1 c, hv.2.2.2.2.2.1 c, hv.2.2.2.2.2.2.1 c,
    hv.2.2.2.2.2.2.2 c⟩

variable (v : SLA p) (η : ℝ)

variable {v η}

lemma rdata_pos {rd : ∀ c, RData p (v.G c)} {c : v.C} {a t : ZMod p} (h : v.Ref η c a t) :
    v.rdata η rd (c, a, t) = (v.ldata c).refine (rd c) a t (v.tau η c) := by
  classical
  unfold rdata; rw [if_pos h]

lemma rdata_neg {rd : ∀ c, RData p (v.G c)} {c : v.C} {a t : ZMod p} (h : ¬ v.Ref η c a t) :
    v.rdata η rd (c, a, t) = v.ldata c := by
  classical
  unfold rdata; rw [if_neg h]

lemma sig_nonneg (hv : v.Valid) (c : v.C) (hη : 0 < η) : 0 ≤ v.sig η c := by
  have := (hv.2.2.2.1 c).1
  unfold sig p71R lqR lqτ p71δ wρh wδ wP eps4
  positivity

lemma rprob_nonneg (hv : v.Valid) (c' : v.C × ZMod p × ZMod p) : 0 ≤ v.rprob η c' :=
  mul_nonneg (mul_nonneg (hv.1 _) (regP_nonneg _ _)) (regP_nonneg _ _)

lemma sum_rprob (hv : v.Valid) (hη : 0 < η) : ∑ c', v.rprob η c' = 1 := by
  unfold rprob
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [← hv.2.1]
  refine sum_congr rfl fun c _ => ?_
  simp_rw [mul_assoc, ← mul_sum, ← sum_mul]
  rw [sum_regP _ (sig_nonneg hv c hη), sum_regP_center _ (by linarith [(hv.2.2.2.1 c).1]), one_mul,
    mul_one]

/-- Validity of a refined label. -/
lemma refine_OK (hp : p.Prime) {L : LData p} (hL : L.OK) (r : RData p L.G) {a t : ZMod p}
    {τ σ : ℝ} (hGood : (L.G.sub r.B).Good) (hm : ((2 * r.m : ℕ) : ZMod p) ≠ 0)
    (ha : snorm L.S (a - L.n) ≤ L.ρ / 2) (ht : snorm L.S t ≤ σ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hbud : L.ρ / 2 + σ + 2 * r.m * τ ≤ L.ρ) : (L.refine r a t τ).OK := by
  classical
  haveI := Fact.mk hp
  obtain ⟨⟨s, hs, hs0⟩, ⟨hρ0, hρ1⟩, hLip, hF1, hLQ, -⟩ := hL
  refine ⟨⟨s * ((2 * r.m : ℕ) : ZMod p)⁻¹, mem_image_of_mem _ (mem_insert_of_mem hs),
    mul_ne_zero hs0 (inv_ne_zero hm)⟩, ⟨hτ0, hτ1⟩, DTorus.isLip_sub hLip r.B _, fun x => hF1 _, ?_,
    hGood⟩
  change LocQuad (sBohr _ (a + t) τ) (fun x => r.π (L.Ξ x - L.Ξ (a + t)))
  refine ((hLQ.mono ?_).sub_const _).comp r.π
  intro x hx
  rw [mem_sBohr hτ0.le] at hx
  rw [mem_sBohr hρ0.le]
  have h1 : snorm L.S (x - (a + t)) ≤ (2 * r.m : ℕ) * τ := by
    refine (snorm_mono (subset_insert (r.ξ a) L.S) _).trans ?_
    refine (snorm_le_of_image_inv hp _ _ hm _).trans ?_
    exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
  have e : x - L.n = (a - L.n) + t + (x - (a + t)) := by abel
  rw [e]
  refine (snorm_add_le _ _).trans ?_
  have := snorm_add_le (S := L.S) (a - L.n) t
  push_cast at h1
  linarith

/-- Validity of the refined approximant. -/
theorem refined_valid (hp : p.Prime) (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hR : ∀ c, v.Poor η c → v.RProp η c (rd c)) (hN : ∀ c, v.Poor η c → v.NumOK η c (rd c)) :
    (v.refined η rd).Valid := by
  refine ofData_valid _ _ _ (rprob_nonneg hv) (sum_rprob hv hη) ?_
  rintro ⟨c, a, t⟩
  by_cases h : v.Ref η c a t
  · rw [rdata_pos h]
    obtain ⟨hpoor, ha, ht⟩ := h
    obtain ⟨hm1, -, -, hGood, -, -, -⟩ := hR c hpoor
    obtain ⟨hs0, hs8, hτ0, hτ1, -, h4m, -, -, -, hm⟩ := hN c hpoor
    have hρ0 := (hv.2.2.2.1 c).1
    refine refine_OK hp (ldata_OK hv c) (rd c) (σ := v.sig η c) hGood hm ?_ ?_ hτ0 hτ1 ?_
    · exact snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) ha) (by positivity)
    · exact snorm_le_of_mem (mem_bohr_of_regP_ne_zero hs0.le ht) hs0.le
    · change v.ρ c / 2 + v.sig η c + 2 * (rd c).m * v.tau η c ≤ v.ρ c
      nlinarith
  · rw [rdata_neg h]; exact ldata_OK hv c

/-! ### Statistics of the refined approximant -/

lemma sum_refined (rd : ∀ c, RData p (v.G c)) (Φ : LData p → ℝ) :
    ∑ c', v.rprob η c' * Φ (v.rdata η rd c') =
      ∑ c, v.prob c * ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
        ∑ t, regP (v.S c) (v.sig η c) t * Φ (v.rdata η rd (c, a, t)) := by
  unfold rprob
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => ?_
  simp_rw [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun t _ => ?_
  ring

lemma inner_nonpoor (hv : v.Valid) (hη : 0 < η) (rd : ∀ c, RData p (v.G c)) {c : v.C}
    (hc : ¬ v.Poor η c) (Φ : LData p → ℝ) :
    ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
      ∑ t, regP (v.S c) (v.sig η c) t * Φ (v.rdata η rd (c, a, t)) = Φ (v.ldata c) := by
  have e : ∀ a t, v.rdata η rd (c, a, t) = v.ldata c := fun a t => rdata_neg (fun h => hc h.1)
  simp_rw [e, ← sum_mul, sum_regP _ (sig_nonneg hv c hη), one_mul]
  rw [sum_regP_center _ (by linarith [(hv.2.2.2.1 c).1]), one_mul]

lemma inner_poor_le (rd : ∀ c, RData p (v.G c)) {c : v.C} (hc : v.Poor η c)
    (Φ : LData p → ℝ) (Ψ : ZMod p → ZMod p → ℝ)
    (hΦ : ∀ a t, v.Ref η c a t → Φ ((v.ldata c).refine (rd c) a t (v.tau η c)) ≤ Ψ a t) :
    ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
      ∑ t, regP (v.S c) (v.sig η c) t * Φ (v.rdata η rd (c, a, t)) ≤
    ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) * ∑ t, regP (v.S c) (v.sig η c) t * Ψ a t := by
  refine sum_le_sum fun a _ => ?_
  by_cases ha : regP (v.S c) (v.ρ c / 2) (a - v.n c) = 0
  · simp [ha]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => ?_) (regP_nonneg _ _)
  by_cases ht : regP (v.S c) (v.sig η c) t = 0
  · simp [ht]
  have hR : v.Ref η c a t := ⟨hc, ha, ht⟩
  rw [rdata_pos hR]
  exact mul_le_mul_of_nonneg_left (hΦ a t hR) (regP_nonneg _ _)

lemma inner_poor_eq (rd : ∀ c, RData p (v.G c)) {c : v.C} (hc : v.Poor η c)
    (Φ : LData p → ℝ) (Ψ : ZMod p → ZMod p → ℝ)
    (hΦ : ∀ a t, v.Ref η c a t → Φ ((v.ldata c).refine (rd c) a t (v.tau η c)) = Ψ a t) :
    ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) *
      ∑ t, regP (v.S c) (v.sig η c) t * Φ (v.rdata η rd (c, a, t)) =
    ∑ a, regP (v.S c) (v.ρ c / 2) (a - v.n c) * ∑ t, regP (v.S c) (v.sig η c) t * Ψ a t := by
  refine le_antisymm (inner_poor_le rd hc Φ Ψ fun a t h => (hΦ a t h).le) ?_
  have := inner_poor_le rd hc (fun L => -Φ L) (fun a t => -Ψ a t) fun a t h => (neg_le_neg_iff.mpr
    (hΦ a t h).ge)
  simp only [mul_neg, sum_neg_distrib, neg_le_neg_iff] at this
  exact this

lemma avg_shift (L : LData p) (g : ZMod p → ℝ) :
    L.avg g = ∑ y, regP L.S (L.ρ / 2) y * g (L.n + y) := by
  unfold LData.avg
  exact (Fintype.sum_equiv (Equiv.addLeft L.n) _ _ fun y => by simp).symm

/-- The dilated frequency set of the label `(c, a, ·)`. -/
def rS (rd : ∀ c, RData p (v.G c)) (c : v.C) (a : ZMod p) : Finset (ZMod p) :=
  (insert ((rd c).ξ a) (v.S c)).image (fun s => s * ((2 * (rd c).m : ℕ) : ZMod p)⁻¹)

lemma snorm_le_of_rS (hp : p.Prime) (rd : ∀ c, RData p (v.G c)) {c : v.C}
    (hm : ((2 * (rd c).m : ℕ) : ZMod p) ≠ 0) (a y : ZMod p) :
    snorm (v.S c) y ≤ (2 * (rd c).m : ℕ) * snorm (v.rS rd c a) y :=
  (snorm_mono (subset_insert _ _) _).trans (snorm_le_of_image_inv hp _ _ hm _)

/-- **Waste**: the expectation of a bounded function barely changes. -/
theorem ex_refined (hp : p.Prime) (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hR : ∀ c, v.Poor η c → v.RProp η c (rd c)) (hN : ∀ c, v.Poor η c → v.NumOK η c (rd c))
    (g : ZMod p → ℝ) {B : ℝ} (hg : ∀ x, |g x| ≤ B) :
    |((v.refined η rd).triple η).ex g - (v.triple η).ex g| ≤ B * (η ^ C3 / 4) := by
  have heps : 0 ≤ eps4 η := (Real.exp_pos _).le
  have hv' := refined_valid hp hv hη hR hN
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg 0)
  rw [ex_eq _ η heps (fun c' => (hv'.2.2.2.1 c').1.le),
    ex_eq v η heps (fun c => (hv.2.2.2.1 c).1.le)]
  change |∑ c', v.rprob η c' * (v.rdata η rd c').avg g - _| ≤ _
  rw [sum_refined _ (fun L => L.avg g), ← sum_sub_distrib]
  simp_rw [← mul_sub]
  refine abs_wavg_le hv.1 hv.2.1 _ fun c _ => ?_
  by_cases hc : v.Poor η c
  · obtain ⟨hm1, -, -, -, -, -, -⟩ := hR c hc
    obtain ⟨hs0, hs8, hτ0, -, -, h4m, hnum, -, -, hm⟩ := hN c hc
    have hρ0 := (hv.2.2.2.1 c).1
    have hin := inner_poor_eq rd hc (fun L => L.avg g)
      (fun a t => ∑ y, regP (v.rS rd c a) (v.tau η c / 2) y * g (a + t + y)) (fun a t _ => by
        beta_reduce; rw [avg_shift]; rfl)
    beta_reduce at hin
    rw [hin]
    have hmix := tv_mix (S := v.S c) (n0 := v.n c) hρ0 hs0
      (mul_nonneg (Nat.cast_nonneg _) hτ0.le) h4m hs8
      (fun a y => regP (v.rS rd c a) (v.tau η c / 2) y) (fun a y => regP_nonneg _ _)
      (fun a => sum_regP _ (by positivity)) (fun a y hy => by
        have hyb := snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by positivity) hy)
          (by positivity)
        have := snorm_le_of_rS hp rd hm a y
        push_cast at this
        nlinarith [Nat.cast_nonneg (α := ℝ) (rd c).m]) g hg
    refine hmix.trans ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hnum hB
  · have hin := inner_nonpoor hv hη rd hc (fun L => L.avg g)
    beta_reduce at hin
    rw [hin]
    simp only [sub_self, abs_zero]
    have : (0 : ℝ) ≤ η ^ C3 := by positivity
    positivity

/-! ### Structural statistics -/

lemma condLam_refined {rd : ∀ c, RData p (v.G c)} {c' : v.C × ZMod p × ZMod p} {c : v.C}
    (hD : v.rdata η rd c' = v.ldata c) : (v.refined η rd).condLam η c' = v.condLam η c := by
  unfold SLA.condLam SLA.triple refined ofData
  try simp only
  rw [hD]; rfl

lemma condEx_refined {rd : ∀ c, RData p (v.G c)} {c' : v.C × ZMod p × ZMod p} {c : v.C}
    (hD : v.rdata η rd c' = v.ldata c) : (v.refined η rd).condEx η c' = v.condEx η c := by
  unfold SLA.condEx SLA.triple refined ofData
  try simp only
  rw [hD]; rfl

lemma poor_refined {rd : ∀ c, RData p (v.G c)} {c' : v.C × ZMod p × ZMod p}
    (h : (v.refined η rd).Poor η c') : v.Ref η c'.1 c'.2.1 c'.2.2 := by
  obtain ⟨c, a, t⟩ := c'
  obtain ⟨hpr, hlt⟩ := h
  change v.rprob η (c, a, t) ≠ 0 at hpr
  unfold rprob at hpr
  simp only [ne_eq, mul_eq_zero, not_or] at hpr
  obtain ⟨⟨hc0, ha⟩, ht⟩ := hpr
  refine ⟨?_, ha, ht⟩
  by_contra hc
  have hD : v.rdata η rd (c, a, t) = v.ldata c := rdata_neg fun h => hc h.1
  rw [condLam_refined hD, condEx_refined hD] at hlt
  exact hc ⟨hc0, hlt⟩

lemma exists_poor (hv : v.Valid) (hlow : (v.triple η).lamF ≤ (v.triple η).exF ^ 4 - η)
    (hη : 0 < η) : ∃ c, v.Poor η c := by
  by_contra hno
  push_neg at hno
  have hc : ∀ c, v.prob c * (v.condEx η c ^ 4 - η / 2) ≤ v.prob c * v.condLam η c := by
    intro c
    by_cases h0 : v.prob c = 0
    · simp [h0]
    · have : ¬ v.condLam η c < v.condEx η c ^ 4 - η / 2 := fun h => hno c ⟨h0, h⟩
      exact mul_le_mul_of_nonneg_left (not_lt.mp this) (hv.1 c)
  have hlam : (v.triple η).lamF = ∑ c, v.prob c * v.condLam η c := rfl
  have hex : (v.triple η).exF = ∑ c, v.prob c * v.condEx η c := rfl
  have hJ : (∑ c, v.prob c * v.condEx η c) ^ 4 ≤ ∑ c, v.prob c * v.condEx η c ^ 4 := by
    have := (Even.convexOn_pow (𝕜 := ℝ) (n := 4) (by decide)).map_sum_le (t := univ)
      (w := v.prob) (p := fun c => v.condEx η c) (fun c _ => hv.1 c) hv.2.1
      (fun _ _ => Set.mem_univ _)
    simpa [smul_eq_mul] using this
  have h1 : ∑ c, v.prob c * (v.condEx η c ^ 4 - η / 2) =
      ∑ c, v.prob c * v.condEx η c ^ 4 - η / 2 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hv.2.1, one_mul]
  have h2 := sum_le_sum fun c (_ : c ∈ univ) => hc c
  rw [h1, ← hlam] at h2
  rw [hex] at hlow
  linarith

lemma nonempty_C (hv : v.Valid) : Nonempty v.C := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hv.2.1
  rw [Finset.univ_eq_empty, sum_empty] at this
  exact zero_ne_one this

theorem d2p_refined (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hR : ∀ c, v.Poor η c → v.RProp η c (rd c))
    (hlow : (v.triple η).lamF ≤ (v.triple η).exF ^ 4 - η) :
    (v.refined η rd).d2p η + 1 ≤ v.d2p η := by
  classical
  have hle : ∀ c, v.Poor η c → (v.G c).d ≤ v.d2p η := fun c hc =>
    Finset.le_sup (f := fun c => (v.G c).d) (mem_filter.mpr ⟨mem_univ _, hc⟩)
  obtain ⟨c0, hc0⟩ := exists_poor hv hlow hη
  have h1 : 1 ≤ v.d2p η := by
    have := (hR c0 hc0).2.2.1
    have := hle c0 hc0
    omega
  have h2 : (v.refined η rd).d2p η ≤ v.d2p η - 1 := by
    unfold SLA.d2p
    refine Finset.sup_le fun c' hc' => ?_
    have hp' := poor_refined (mem_filter.mp hc').2
    obtain ⟨c, a, t⟩ := c'
    change (v.rdata η rd (c, a, t)).G.d ≤ _
    rw [rdata_pos hp']
    change (rd c).d' ≤ _
    have := (hR c hp'.1).2.2.1
    have := hle c hp'.1
    have hh : v.d2p η = (univ.filter fun c => v.Poor η c).sup fun c => (v.G c).d := rfl
    omega
  omega

theorem d2_refined {rd : ∀ c, RData p (v.G c)} (hR : ∀ c, v.Poor η c → v.RProp η c (rd c)) :
    (v.refined η rd).d2 ≤ v.d2 := by
  unfold SLA.d2
  refine Finset.sup_le fun c' _ => ?_
  obtain ⟨c, a, t⟩ := c'
  have hc : (v.G c).d ≤ univ.sup fun c => (v.G c).d := Finset.le_sup (f := fun c => (v.G c).d)
    (mem_univ c)
  change (v.rdata η rd (c, a, t)).G.d ≤ _
  by_cases h : v.Ref η c a t
  · rw [rdata_pos h]
    change (rd c).d' ≤ _
    have := (hR c h.1).2.2.1
    omega
  · rw [rdata_neg h]; exact hc

theorem d1_refined (rd : ∀ c, RData p (v.G c)) : (v.refined η rd).d1 ≤ v.d1 + 1 := by
  classical
  unfold SLA.d1
  refine Finset.sup_le fun c' _ => ?_
  obtain ⟨c, a, t⟩ := c'
  have hc : (v.S c).card ≤ univ.sup fun c => (v.S c).card :=
    Finset.le_sup (f := fun c => (v.S c).card) (mem_univ c)
  change (v.rdata η rd (c, a, t)).S.card ≤ _
  by_cases h : v.Ref η c a t
  · rw [rdata_pos h]
    change ((insert ((rd c).ξ a) (v.S c)).image _).card ≤ _
    have := card_image_le (s := insert ((rd c).ξ a) (v.S c))
      (f := fun s => s * ((2 * (rd c).m : ℕ) : ZMod p)⁻¹)
    have := card_insert_le ((rd c).ξ a) (v.S c)
    omega
  · rw [rdata_neg h]; change (v.S c).card ≤ _; omega

theorem rmin_refined (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hN : ∀ c, v.Poor η c → v.NumOK η c (rd c)) :
    Real.exp (-(1 / η) ^ C5) * v.rmin ≤ (v.refined η rd).rmin := by
  haveI := nonempty_C hv
  have hle : ∀ c, v.rmin ≤ v.ρ c := fun c => by
    unfold SLA.rmin; exact ciInf_le (Finite.bddBelow_range _) c
  have he1 : Real.exp (-(1 / η) ^ C5) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have he0 := Real.exp_pos (-(1 / η) ^ C5)
  haveI : Nonempty (v.refined η rd).C := (inferInstance : Nonempty (v.C × ZMod p × ZMod p))
  unfold SLA.rmin
  refine le_ciInf fun c' => ?_
  obtain ⟨c, a, t⟩ := c'
  change _ ≤ (v.rdata η rd (c, a, t)).ρ
  have hρ0 := (hv.2.2.2.1 c).1
  by_cases h : v.Ref η c a t
  · rw [rdata_pos h]
    change _ ≤ v.tau η c
    refine le_trans ?_ (hN c h.1).2.2.2.2.1
    exact mul_le_mul_of_nonneg_left (hle c) he0.le
  · rw [rdata_neg h]
    change _ ≤ v.ρ c
    have := hle c
    have : Real.exp (-(1 / η) ^ C5) * ⨅ c, v.ρ c ≤ 1 * ⨅ c, v.ρ c := by
      apply mul_le_mul_of_nonneg_right he1
      exact le_ciInf fun c => (hv.2.2.2.1 c).1.le
    change Real.exp (-(1 / η) ^ C5) * v.rmin ≤ v.ρ c
    unfold SLA.rmin at *
    linarith

theorem volm_refined (hv : v.Valid) (hη : 0 < η) {rd : ∀ c, RData p (v.G c)}
    (hR : ∀ c, v.Poor η c → v.RProp η c (rd c)) (hN : ∀ c, v.Poor η c → v.NumOK η c (rd c)) :
    (v.refined η rd).volm ≤ Real.exp ((1 / η) ^ C3) * v.volm := by
  haveI := nonempty_C hv
  have hle : ∀ c, (v.G c).vol ≤ v.volm := fun c => by
    unfold SLA.volm; exact le_ciSup (Finite.bddAbove_range (fun c => (v.G c).vol)) c
  have he1 : 1 ≤ Real.exp ((1 / η) ^ C3) := by
    rw [Real.one_le_exp_iff]; positivity
  have hvol0 : ∀ c, 0 ≤ (v.G c).vol := fun c => by
    unfold DTorus.vol; exact prod_nonneg fun i _ => norm_nonneg _
  have hvm0 : 0 ≤ v.volm := (hvol0 (Classical.arbitrary _)).trans (hle _)
  unfold SLA.volm
  haveI : Nonempty (v.refined η rd).C := (inferInstance : Nonempty (v.C × ZMod p × ZMod p))
  refine ciSup_le fun c' => ?_
  obtain ⟨c, a, t⟩ := c'
  change (v.rdata η rd (c, a, t)).G.vol ≤ _
  by_cases h : v.Ref η c a t
  · rw [rdata_pos h]
    change ((v.G c).sub (rd c).B).vol ≤ _
    refine (hR c h.1).2.2.2.2.1.trans ?_
    have hf := (hN c h.1).2.2.2.2.2.2.2.2.1
    have := hle c
    unfold SLA.volm at this
    calc _ ≤ Real.exp ((1 / η) ^ C3) * (v.G c).vol :=
          mul_le_mul_of_nonneg_right hf (hvol0 c)
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  · rw [rdata_neg h]
    change (v.G c).vol ≤ _
    have := hle c
    unfold SLA.volm at this hvm0
    nlinarith

end SLA

lemma exp_gap {u : ℝ} (hu : 10 ≤ u) {a b : ℕ} (hab : a + 1 ≤ b) :
    2 * Real.exp (u ^ a) < Real.exp (u ^ b) := by
  have hc : u ^ a + 1 ≤ u ^ b := by
    have h1 : u ^ (a + 1) ≤ u ^ b := pow_le_pow_right₀ (by linarith) hab
    have h2 : u ^ (a + 1) = u ^ a * u := pow_succ _ _
    have h3 : (1 : ℝ) ≤ u ^ a := one_le_pow₀ (by linarith)
    nlinarith
  calc 2 * Real.exp (u ^ a) < Real.exp 1 * Real.exp (u ^ a) := by
        have := Real.exp_one_gt_d9
        have := Real.exp_pos (u ^ a)
        nlinarith
    _ = Real.exp (u ^ a + 1) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := Real.exp_le_exp.mpr hc

set_option maxHeartbeats 4000000 in
/-- **Theorem 6.7** (bad lower bound implies dimension decrement). -/
theorem bad_dim_thm {p : ℕ} [NeZero p] (hp : p.Prime) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
    (hpη : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) {f : ZMod p → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {v : SLA p} (hv : v.Valid) (hb : v.Bounds η)
    (hlow : (v.triple η).lamF ≤ (v.triple η).exF ^ 4 - η) :
    ∃ v' : SLA p, v'.Valid ∧ v.Edge η f v' ∧ v'.d2 ≤ v.d2 ∧ v'.d2p η + 1 ≤ v.d2p η ∧
      (v'.triple η).energy f ≤ (v.triple η).energy f + η ^ (3 * C2) := by
  classical
  haveI := Fact.mk hp
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  set u := 1 / η with hu
  have hu10 : 10 ≤ u := by rw [hu, le_div_iff₀ hη0]; linarith
  have hSc : ∀ c, ((v.S c).card : ℝ) ≤ 65 * u ^ (3 * C2) := by
    intro c
    have : (v.S c).card ≤ v.d1 := Finset.le_sup (f := fun c => (v.S c).card) (mem_univ c)
    exact (Nat.cast_le.mpr this).trans hb1
  have hGd : ∀ c, ((v.G c).d : ℝ) ≤ 64 * u ^ (2 * C2) := by
    intro c
    have : (v.G c).d ≤ v.d2 := Finset.le_sup (f := fun c => (v.G c).d) (mem_univ c)
    exact (Nat.cast_le.mpr this).trans hb2
  have hvol : ∀ c, (v.G c).vol ≤ Real.exp (u ^ (2 * C3)) := by
    intro c
    have : (v.G c).vol ≤ v.volm := by
      unfold SLA.volm; exact le_ciSup (Finite.bddAbove_range (fun c => (v.G c).vol)) c
    exact this.trans hb4
  have heps0 : 0 < SLA.eps4 η := Real.exp_pos _
  have heps8 : SLA.eps4 η ≤ 1 / 8 := by
    unfold SLA.eps4
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h1 : (10 : ℝ) ≤ (1 / η) ^ C4 := by
      rw [← hu]
      calc (10 : ℝ) ≤ u := hu10
        _ = u ^ 1 := (pow_one u).symm
        _ ≤ u ^ C4 := pow_le_pow_right₀ (by linarith) (by unfold C4; norm_num)
    have := Real.add_one_le_exp ((1 / η) ^ C4)
    rw [show ((1 : ℝ) / 8)⁻¹ = 8 by norm_num]
    linarith
  have hex : ∀ c, ∃ r : RData p (v.G c), v.Poor η c → v.RProp η c r ∧ v.NumOK η c r := by
    intro c
    by_cases hc : v.Poor η c
    · have hρ := hv.2.2.2.1 c
      obtain ⟨s0, hs0, -⟩ := hv.2.2.1 c
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := label_num hη0 hη1 ⟨s0, hs0⟩
        (hv.2.2.2.2.2.2.2 c) (hSc c) (hGd c) (hvol c) hρ.1 hρ.2
      obtain ⟨m, ξ, d', B, π, w, hm1, hmb, hd', hG', hvol', hw, herr⟩ :=
        poor_refine hp (hv.2.2.1 c) hρ.1 heps0 heps8 (hv.2.2.2.2.2.2.2 c) (hv.2.2.2.2.1 c)
          (hv.2.2.2.2.2.1 c) (hv.2.2.2.2.2.2.1 c) hη0 (by linarith) n1 hc.2
      obtain ⟨k1, k2, k3⟩ := n9 m hm1 hmb w hw
      refine ⟨⟨m, ξ, d', B, π, w⟩, fun _ => ⟨⟨hm1, hmb, hd', hG', hvol', hw, herr⟩,
        n2, n3, n4, n5, n6, k1, k2, k3, n7, ?_⟩⟩
      -- `2m` is invertible modulo `p`
      have hm2 : (2 * m : ℝ) < p := by
        have h1 : (2 * m : ℝ) ≤ 2 * Real.exp (u ^ C4) := by linarith
        have h2 : 2 * Real.exp (u ^ C4) < Real.exp (u ^ (3 * C5)) := by
          have h45 : C4 + 1 ≤ 3 * C5 := by
            have : C4 < C5 := by
              unfold C4 C5; exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)
            omega
          exact exp_gap hu10 h45
        linarith
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      have hpos : 0 < 2 * m := by omega
      have := Nat.le_of_dvd hpos h0
      have : (p : ℝ) ≤ 2 * m := by exact_mod_cast this
      linarith
    · exact ⟨⟨0, fun _ => 0, 0, 0, 0, 0⟩, fun h => absurd h hc⟩
  choose rd hrd using hex
  have hR : ∀ c, v.Poor η c → v.RProp η c (rd c) := fun c h => (hrd c h).1
  have hN : ∀ c, v.Poor η c → v.NumOK η c (rd c) := fun c h => (hrd c h).2
  have hC3 : (0 : ℝ) ≤ η ^ C3 := by positivity
  refine ⟨v.refined η rd, SLA.refined_valid hp hv hη0 hR hN, ⟨?_, ?_, ?_, ?_, ?_⟩,
    SLA.d2_refined hR, SLA.d2p_refined hv hη0 hR hlow, ?_⟩
  · have := SLA.d1_refined (η := η) rd
    have h1 : ((v.refined η rd).d1 : ℝ) ≤ v.d1 + 1 := by exact_mod_cast this
    have : (1 : ℝ) ≤ (1 / η) ^ C2 := one_le_pow₀ (by linarith)
    linarith
  · have := SLA.d2_refined hR; omega
  · exact SLA.rmin_refined hv hη0 hN
  · exact SLA.volm_refined hv hη0 hR hN
  · have := SLA.ex_refined hp hv hη0 hR hN f (B := 1) (fun x => by
      rw [abs_le]; constructor <;> linarith [hf x])
    unfold SLA.waste
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [abs_sub_comm]
    have e : ((v.refined η rd).triple η).ex f - ∑ x, f x / p -
        ((v.triple η).ex f - ∑ x, f x / p) =
        ((v.refined η rd).triple η).ex f - (v.triple η).ex f := by ring
    rw [e]
    linarith
  · have := SLA.energy_refined hp hv hη0 hR hN f hf
    have h2 : 2 * η ^ C3 ≤ η ^ (3 * C2) := by
      have hc : 3 * C2 + 1 ≤ C3 := by unfold C2 C3; norm_num
      have : η ^ C3 ≤ η ^ (3 * C2 + 1) := pow_le_pow_of_le_one hη0.le (by linarith) hc
      rw [pow_succ] at this
      have : 0 ≤ η ^ (3 * C2) := by positivity
      nlinarith
    linarith

end

end GT
end File_GT_BadDim

open Finset KM Matrix
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
    (hpη : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) {f : ZMod p → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {v : SLA p} (hv : v.Valid) (hb : v.Bounds η)
    (hlow : (v.triple η).lamF ≤ (v.triple η).exF ^ 4 - η) :
    ∃ v' : SLA p, v'.Valid ∧ v.Edge η f v' ∧ v'.d2 ≤ v.d2 ∧ v'.d2p η + 1 ≤ v.d2p η ∧
      (v'.triple η).energy f ≤ (v.triple η).energy f + η ^ (3 * C2) :=
  @GT.bad_dim_thm p _ hp η hη0 hη1 hpη f hf v hv hb hlow

