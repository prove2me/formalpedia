-- Prove2me | solution 1 for GT.large_quad
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:43:46.163074+00:00
-- url     : https://prove2.me/submissions/d05d68ca-9c87-4d3f-a20c-77a62e1d651b

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

lemma ec_add (x y : UnitAddCircle) : ec (x + y) = ec x * ec y := by
  simp [ec, AddCircle.toCircle_add]

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

lemma map_zsmul (h : AddOn S R f) (n : ℤ) (x : ZMod p) (hn : 2 * |(n : ℝ)| * snorm S x ≤ R) :
    f ((n : ZMod p) * x) = n • f x := by
  have hs := snorm_nonneg (S := S) x
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp only [Int.cast_natCast, Nat.abs_cast] at hn ⊢
    rw [h.map_nsmul m x (by nlinarith), natCast_zsmul]
  · simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] at hn ⊢
    rw [neg_mul, h.map_neg _ ?_, h.map_nsmul m x (by nlinarith), neg_smul, natCast_zsmul]
    exact le_trans (by linarith [snorm_nsmul_le (S := S) m x]) hn

end AddOn

lemma snorm_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℤ) (x : ι → ZMod p) :
    snorm S (∑ i ∈ s, (c i : ZMod p) * x i) ≤ ∑ i ∈ s, |(c i : ℝ)| * snorm S (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, sum_insert hj]
    exact (snorm_add_le _ _).trans (add_le_add (snorm_intsmul_le _ _) ih)

lemma AddOn.map_sum {R : ℝ} {f : ZMod p → M} (h : AddOn S R f) {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (x : ι → ZMod p) (hs : 2 * ∑ i ∈ s, |(c i : ℝ)| * snorm S (x i) ≤ R) :
    f (∑ i ∈ s, (c i : ZMod p) * x i) = ∑ i ∈ s, c i • f (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty] at hs ⊢
    exact h.map_zero (by linarith)
  | insert j s hj ih =>
    rw [sum_insert hj] at hs
    have h1 : 0 ≤ |(c j : ℝ)| * snorm S (x j) := mul_nonneg (abs_nonneg _) (snorm_nonneg _)
    have h2 : 0 ≤ ∑ i ∈ s, |(c i : ℝ)| * snorm S (x i) :=
      sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (snorm_nonneg _)
    rw [sum_insert hj, sum_insert hj, h _ _ ?_, h.map_zsmul _ _ (by linarith), ih (by linarith)]
    exact le_trans (add_le_add (snorm_intsmul_le _ _) (snorm_sum_le s c x)) (by linarith)

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

lemma norm_coe_real_eq {s : ℝ} (h : |s| ≤ 1 / 2) : ‖(s : UnitAddCircle)‖ = |s| :=
  (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using h)

lemma ec_nsmul (x : UnitAddCircle) (n : ℕ) : ec (n • x) = ec x ^ n := by
  induction n with
  | zero => simp [ec]
  | succ n ih => rw [succ_nsmul, ec_add, ih, pow_succ]

/-- The geometric sum bound `|∑_{b<M} e(bx)| ≤ 1/(2‖x‖)`. -/
lemma norm_geom_le (x : UnitAddCircle) (M : ℕ) :
    2 * ‖x‖ * ‖∑ b ∈ range M, ec (b • x)‖ ≤ 1 := by
  have e : (∑ b ∈ range M, ec (b • x)) * (ec x - 1) = ec (M • x) - 1 := by
    simp only [ec_nsmul]; exact geom_sum_mul _ _
  have h1 : ‖∑ b ∈ range M, ec (b • x)‖ * ‖ec x - 1‖ ≤ 2 := by
    rw [← norm_mul, e]
    refine (norm_sub_le _ _).trans ?_
    simp; norm_num
  have h4 := four_norm_le x
  have h0 : 0 ≤ ‖∑ b ∈ range M, ec (b • x)‖ := norm_nonneg _
  nlinarith

lemma norm_geom_le' (x : UnitAddCircle) (M : ℕ) : ‖∑ b ∈ range M, ec (b • x)‖ ≤ M := by
  refine (norm_sum_le _ _).trans ?_
  simp

set_option maxHeartbeats 1000000 in
/-- **Vinogradov's lemma**, unwindowed form. -/
lemma vino0 {W : ℕ} {G : Finset ℕ} (hG : G ⊆ range W) {σ ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hcard : σ * W ≤ G.card) {θ β : UnitAddCircle} (hb : ∀ b ∈ G, ‖b • θ + β‖ ≤ ε)
    (hεW : 8 * ε * W ≤ 1) (hW : 8 ≤ σ ^ 2 * W) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 2 / σ ∧ ‖k • θ‖ ≤ 8 * ε / (σ ^ 2 * W) := by
  have hW0 : (0 : ℝ) < W := by
    by_contra h; push_neg at h; nlinarith [sq_nonneg σ]
  have hε0 : 0 ≤ ε := by
    obtain ⟨b, hb'⟩ : G.Nonempty := by
      rw [← Finset.card_pos]; have : (0 : ℝ) < G.card := by nlinarith
      exact_mod_cast this
    exact (norm_nonneg _).trans (hb b hb')
  have hσW : 8 ≤ σ * W := by nlinarith
  -- step 1: two elements at distance < g
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = ⌈2 / σ⌉₊ := ⟨_, rfl⟩
  have hg1 : 2 / σ ≤ g := by rw [hg]; exact Nat.le_ceil _
  have hg2 : (g : ℝ) < 2 / σ + 1 := by rw [hg]; exact Nat.ceil_lt_add_one (by positivity)
  have hgpos : 0 < g := by
    have : (0 : ℝ) < g := lt_of_lt_of_le (by positivity) hg1
    exact_mod_cast this
  have hlt : (range ((W - 1) / g + 1)).card < G.card := by
    rw [card_range]
    have h1 : ((W - 1) / g : ℕ) * g ≤ W - 1 := Nat.div_mul_le_self _ _
    have h2 : (((W - 1) / g : ℕ) : ℝ) * g ≤ W := by
      have : (((W - 1) / g : ℕ) : ℝ) * g ≤ ((W - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      refine this.trans ?_
      exact_mod_cast Nat.sub_le W 1
    have h3 : (((W - 1) / g : ℕ) : ℝ) ≤ σ * W / 2 := by
      have hg0 : (0 : ℝ) < g := by exact_mod_cast hgpos
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have : (((W - 1) / g : ℕ) : ℝ) * (2 / σ) ≤ W := by
        refine le_trans ?_ h2
        exact mul_le_mul_of_nonneg_left hg1 (by positivity)
      have e : (((W - 1) / g : ℕ) : ℝ) * (2 / σ) = (((W - 1) / g : ℕ) : ℝ) * 2 / σ := by ring
      rw [e, div_le_iff₀ hσ] at this
      linarith
    have : ((((W - 1) / g + 1 : ℕ)) : ℝ) < G.card := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨b1, hb1, b2, hb2, hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt
    (f := fun b => b / g) (fun b hb => by
      have := mem_range.1 (hG hb)
      simp only [coe_range, Set.mem_Iio]
      refine Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
  -- difference k
  have key : ∀ x y : ℕ, x ∈ G → y ∈ G → x < y → ‖(y - x) • θ‖ ≤ 2 * ε := by
    intro x y hx hy hxy
    have e : (y - x) • θ = (y • θ + β) - (x • θ + β) := by
      rw [add_sub_add_right_eq_sub, sub_nsmul _ hxy.le, sub_eq_add_neg]
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith [hb x hx, hb y hy]
  have gapk : ∃ x y : ℕ, x ∈ G ∧ y ∈ G ∧ x < y ∧ y - x < g := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · refine ⟨b1, b2, hb1, hb2, h, ?_⟩
      have := Nat.div_add_mod b1 g; have := Nat.div_add_mod b2 g
      have := Nat.mod_lt b1 hgpos; have := Nat.mod_lt b2 hgpos
      rw [heq] at *; omega
    · refine ⟨b2, b1, hb2, hb1, h, ?_⟩
      have := Nat.div_add_mod b1 g; have := Nat.div_add_mod b2 g
      have := Nat.mod_lt b1 hgpos; have := Nat.mod_lt b2 hgpos
      rw [heq] at *; omega
  obtain ⟨x, y, hx, hy, hxy, hxyg⟩ := gapk
  obtain ⟨k, hk⟩ : ∃ k, k = y - x := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by omega
  have hkg : (k : ℝ) ≤ 2 / σ := by
    have : k + 1 ≤ g := by omega
    have : (k : ℝ) + 1 ≤ g := by exact_mod_cast this
    linarith
  have hk2 : ‖k • θ‖ ≤ 2 * ε := by rw [hk]; exact key x y hx hy hxy
  refine ⟨k, hk1, hkg, ?_⟩
  -- step 2: a residue class
  have hkpos : 0 < k := hk1
  obtain ⟨r, hr, hfib⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := G) (t := range k) (f := fun b => b % k) (n := G.card / k)
    (fun b _ => mem_range.2 (Nat.mod_lt _ hkpos)) ⟨0, mem_range.2 hkpos⟩
    (by rw [card_range]; exact Nat.mul_div_le _ _)
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, F = {x ∈ G | x % k = r} := ⟨_, rfl⟩
  rw [← hF] at hfib
  have hFG : F ⊆ G := by rw [hF]; exact filter_subset _ _
  have hGk : (G.card : ℝ) / k - 1 ≤ ((G.card / k : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := G.card) hkpos
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hkpos
    rw [div_sub_one hk0.ne', div_le_iff₀ hk0]
    have : (G.card : ℝ) < ((G.card / k : ℕ) : ℝ) * k + k := by exact_mod_cast this
    linarith
  have hFcard : σ ^ 2 * W / 2 - 1 ≤ (F.card : ℝ) := by
    have h1 : σ ^ 2 * W / 2 ≤ (G.card : ℝ) / k := by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hkpos
      rw [le_div_iff₀ hk0]
      have : σ * k ≤ 2 := by rw [le_div_iff₀ hσ] at hkg; linarith
      nlinarith
    have : ((G.card / k : ℕ) : ℝ) ≤ F.card := by exact_mod_cast hfib
    linarith
  have hFne : F.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < F.card := by linarith
    exact_mod_cast this
  obtain ⟨b0, hb0⟩ : ∃ b0, b0 = F.min' hFne := ⟨_, rfl⟩
  obtain ⟨bm, hbm⟩ : ∃ bm, bm = F.max' hFne := ⟨_, rfl⟩
  have hb0F : b0 ∈ F := by rw [hb0]; exact min'_mem _ _
  have hbmF : bm ∈ F := by rw [hbm]; exact max'_mem _ _
  have hmod : ∀ b ∈ F, b % k = r := by
    intro b hb; rw [hF] at hb; exact (mem_filter.1 hb).2
  have hle0 : ∀ b ∈ F, b0 ≤ b := by intro b hb; rw [hb0]; exact min'_le _ _ hb
  have hlem : ∀ b ∈ F, b ≤ bm := by intro b hb; rw [hbm]; exact le_max' _ _ hb
  obtain ⟨t, ht⟩ : ∃ t, t = (bm - b0) / k := ⟨_, rfl⟩
  have hdvd : ∀ b ∈ F, k ∣ b - b0 := by
    intro b hb
    have h1 := hmod b hb; have h2 := hmod b0 hb0F
    exact (Nat.modEq_iff_dvd' (hle0 b hb)).1 (h2.trans h1.symm)
  have hbmt : bm - b0 = t * k := by rw [ht]; exact (Nat.div_mul_cancel (hdvd bm hbmF)).symm
  have hFt : F.card ≤ t + 1 := by
    have : F.card ≤ (range (t + 1)).card := by
      refine card_le_card_of_injOn (fun b => (b - b0) / k) (fun b hb => ?_) (fun a ha b hb hab => ?_)
      · simp only [coe_range, Set.mem_Iio]
        refine Nat.lt_succ_of_le ?_
        rw [ht]; exact Nat.div_le_div_right (by have := hlem b hb; omega)
      · (try simp only at hab)
        have ha' := Nat.div_mul_cancel (hdvd a ha)
        have hb' := Nat.div_mul_cancel (hdvd b hb)
        rw [hab] at ha'
        have := hle0 a ha; have := hle0 b hb
        omega
    rwa [card_range] at this
  have ht1 : σ ^ 2 * W / 4 ≤ (t : ℝ) := by
    have : (F.card : ℝ) ≤ t + 1 := by exact_mod_cast hFt
    nlinarith
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by nlinarith) ht1
  -- linearization
  obtain ⟨s, hs, hs1, _⟩ := exists_rep (k • θ)
  have htk : ((t : ℝ) * k : ℝ) ≤ W := by
    have h1 : t * k ≤ W := by
      rw [← hbmt]; have := mem_range.1 (hG (hFG hbmF)); omega
    exact_mod_cast h1
  have hts : |(t : ℝ) * s| ≤ 1 / 4 := by
    rw [abs_mul, Nat.abs_cast, hs1]
    have ht' : (t : ℝ) ≤ W := by
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      exact le_trans (le_mul_of_one_le_right (by positivity) hk1') htk
    have := mul_le_mul ht' hk2 (norm_nonneg _) (by positivity)
    linarith
  have e2 : (bm - b0) • θ = ((t * s : ℝ) : UnitAddCircle) := by
    rw [hbmt, mul_nsmul', ← hs, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  have h3 : ‖(bm - b0) • θ‖ ≤ 2 * ε := by
    rcases (hle0 bm hbmF).lt_or_eq with hlt' | heq'
    · exact key b0 bm (hFG hb0F) (hFG hbmF) hlt'
    · rw [heq', Nat.sub_self, zero_nsmul, norm_zero]; linarith
  rw [e2, norm_coe_real_eq (by linarith), abs_mul, Nat.abs_cast, hs1] at h3
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (k • θ)]

set_option maxHeartbeats 1000000 in
/-- **Vinogradov's lemma** (windowed form). -/
lemma vino {M W : ℕ} {G : Finset ℕ} (hG : G ⊆ range M) {σ ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hcard : σ * M ≤ G.card) {θ β : UnitAddCircle} (hb : ∀ b ∈ G, ‖b • θ + β‖ ≤ ε)
    (hW1 : 1 ≤ W) (hWM : W ≤ M) (hεW : 8 * ε * W ≤ 1) (hW : 128 ≤ σ ^ 2 * W) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 8 / σ ∧ ‖k • θ‖ ≤ 128 * ε / (σ ^ 2 * W) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hσW : 4 ≤ σ * W := by nlinarith
  obtain ⟨T, hT⟩ : ∃ T, T = (M - 1) / W + 1 := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT]; exact Nat.succ_pos _
  have hT2 : (T : ℝ) ≤ 2 * M / W := by
    have h1 : ((M - 1) / W) * W ≤ M - 1 := Nat.div_mul_le_self _ _
    have h2 : (((M - 1) / W : ℕ) : ℝ) * W ≤ M := by
      have : (((M - 1) / W : ℕ) : ℝ) * W ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      exact this.trans (by exact_mod_cast Nat.sub_le M 1)
    have hM : (W : ℝ) ≤ M := by exact_mod_cast hWM
    rw [le_div_iff₀ hW0, hT]; push_cast; nlinarith
  obtain ⟨s, hs, hfib⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := G) (t := range T) (f := fun b => b / W) (n := G.card / T)
    (fun b hb => by
      have := mem_range.1 (hG hb)
      rw [mem_range, hT]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
    ⟨0, mem_range.2 hTpos⟩ (by rw [card_range]; exact Nat.mul_div_le _ _)
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, F = {x ∈ G | x / W = s} := ⟨_, rfl⟩
  rw [← hF] at hfib
  have hFG : F ⊆ G := by rw [hF]; exact filter_subset _ _
  have hFs : ∀ b ∈ F, b / W = s := by intro b hb; rw [hF] at hb; exact (mem_filter.1 hb).2
  have hFcard : σ / 4 * W ≤ (F.card : ℝ) := by
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
    have h1 : (G.card : ℝ) / T - 1 ≤ ((G.card / T : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := G.card) hTpos
      rw [div_sub_one hT0.ne', div_le_iff₀ hT0]
      have : (G.card : ℝ) < ((G.card / T : ℕ) : ℝ) * T + T := by exact_mod_cast this
      linarith
    have h2 : σ * W / 2 ≤ (G.card : ℝ) / T := by
      rw [le_div_iff₀ hT0]
      calc σ * W / 2 * T ≤ σ * W / 2 * (2 * M / W) :=
            mul_le_mul_of_nonneg_left hT2 (by positivity)
        _ = σ * M := by field_simp
        _ ≤ G.card := hcard
    have : ((G.card / T : ℕ) : ℝ) ≤ F.card := by exact_mod_cast hfib
    linarith
  -- shift the window to `[0, W)`
  obtain ⟨G', hG'⟩ : ∃ G' : Finset ℕ, G' = F.image (fun b => b - s * W) := ⟨_, rfl⟩
  have hlow : ∀ b ∈ F, s * W ≤ b := by
    intro b hb; rw [← hFs b hb]; exact Nat.div_mul_le_self _ _
  have hhigh : ∀ b ∈ F, b < s * W + W := by
    intro b hb
    have := Nat.lt_div_mul_add (a := b) (Nat.lt_of_lt_of_le Nat.zero_lt_one hW1)
    rw [hFs b hb] at this; exact this
  have hG'sub : G' ⊆ range W := by
    intro x hx; rw [hG', mem_image] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    have := hlow b hb; have := hhigh b hb
    rw [mem_range]; omega
  have hG'card : G'.card = F.card := by
    rw [hG']
    refine card_image_of_injOn fun a ha b hb hab => ?_
    have := hlow a ha; have := hlow b hb
    try simp only at hab
    omega
  have hb' : ∀ b ∈ G', ‖b • θ + (β + (s * W) • θ)‖ ≤ ε := by
    intro x hx; rw [hG', mem_image] at hx
    obtain ⟨b, hbF, rfl⟩ := hx
    have e : (b - s * W) • θ + (β + (s * W) • θ) = b • θ + β := by
      rw [← add_assoc, add_right_comm, ← add_nsmul, Nat.sub_add_cancel (hlow b hbF)]
    rw [e]; exact hb b (hFG hbF)
  obtain ⟨k, hk1, hk2, hk3⟩ := vino0 hG'sub (σ := σ / 4) (by positivity) (by linarith)
    (by rw [hG'card]; exact hFcard) hb' hεW (by nlinarith)
  refine ⟨k, hk1, ?_, ?_⟩
  · rw [show 8 / σ = 2 / (σ / 4) by field_simp; norm_num]; exact hk2
  · rw [show 128 * ε / (σ ^ 2 * W) = 8 * ε / ((σ / 4) ^ 2 * W) by field_simp; ring]
    exact hk3

/-- A bilinear exponential sum over a box `[0,M₁) × [0,M₂)` can only be large if the bilinear
coefficient is close to a rational with small denominator. -/
theorem bilin_major {M1 M2 : ℕ} (h12 : M1 ≤ M2) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM1 : 8192 / δ ^ 3 ≤ M1) (θ α β γ : UnitAddCircle)
    (h : δ * M1 * M2 ≤ ‖∑ b ∈ range M1, ∑ b' ∈ range M2, ec ((b * b') • θ + b • α + b' • β + γ)‖) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 16 / δ ∧ ‖k • θ‖ ≤ 8192 / (δ ^ 4 * M1 * M2) := by
  have hM1pos : (0 : ℝ) < M1 := lt_of_lt_of_le (by positivity) hM1
  have hM2pos : (0 : ℝ) < M2 := lt_of_lt_of_le hM1pos (by exact_mod_cast h12)
  obtain ⟨Sb, hSb⟩ : ∃ Sb : ℕ → ℝ, ∀ b, Sb b = ‖∑ b' ∈ range M2, ec (b' • (b • θ + β))‖ :=
    ⟨_, fun _ => rfl⟩
  have hsum : δ * M1 * M2 ≤ ∑ b ∈ range M1, Sb b := by
    refine h.trans ((norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun b _ => ?_)))
    have e : ∑ b' ∈ range M2, ec ((b * b') • θ + b • α + b' • β + γ) =
        ec (b • α + γ) * ∑ b' ∈ range M2, ec (b' • (b • θ + β)) := by
      rw [mul_sum]; refine sum_congr rfl fun b' _ => ?_
      rw [← ec_add, mul_nsmul, nsmul_add]; congr 1; abel
    rw [e, norm_mul, norm_ec, one_mul, hSb]
  have hSle : ∀ b, Sb b ≤ M2 := fun b => by rw [hSb]; exact norm_geom_le' _ _
  have hS0 : ∀ b, 0 ≤ Sb b := fun b => by rw [hSb]; exact norm_nonneg _
  obtain ⟨G, hG⟩ : ∃ G : Finset ℕ, G = (range M1).filter (fun b => δ * M2 / 2 ≤ Sb b) :=
    ⟨_, rfl⟩
  have hGsub : G ⊆ range M1 := by rw [hG]; exact filter_subset _ _
  have hGcard : δ / 2 * M1 ≤ G.card := by
    have e := sum_filter_add_sum_filter_not (range M1) (fun b => δ * M2 / 2 ≤ Sb b) Sb
    have h1 : ∑ b ∈ (range M1).filter (fun b => δ * M2 / 2 ≤ Sb b), Sb b ≤ G.card * M2 := by
      rw [← hG, ← nsmul_eq_mul, ← sum_const]; exact sum_le_sum fun b _ => hSle b
    have h2 : ∑ b ∈ (range M1).filter (fun b => ¬ δ * M2 / 2 ≤ Sb b), Sb b ≤ M1 * (δ * M2 / 2) := by
      calc _ ≤ ∑ b ∈ (range M1).filter (fun b => ¬ δ * M2 / 2 ≤ Sb b), δ * M2 / 2 :=
            sum_le_sum fun b hb => (not_le.1 (mem_filter.1 hb).2).le
        _ ≤ ∑ b ∈ range M1, δ * M2 / 2 :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
    have : δ * M1 * M2 ≤ G.card * M2 + M1 * (δ * M2 / 2) := by linarith
    have : δ / 2 * M1 * M2 ≤ G.card * M2 := by linarith
    exact le_of_mul_le_mul_right (by linarith) hM2pos
  have hGb : ∀ b ∈ G, ‖b • θ + β‖ ≤ 1 / (δ * M2) := by
    intro b hb
    rw [hG, mem_filter] at hb
    have h1 := norm_geom_le (b • θ + β) M2
    rw [← hSb] at h1
    rw [le_div_iff₀ (by positivity)]
    have := hb.2
    nlinarith [norm_nonneg (b • θ + β)]
  obtain ⟨W, hW⟩ : ∃ W, W = min M1 ⌊δ * M2 / 8⌋₊ := ⟨_, rfl⟩
  have hfl : δ * M2 / 16 ≤ (⌊δ * M2 / 8⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one (δ * M2 / 8)
    have h2 : 1024 / δ ^ 2 ≤ δ * M2 / 8 := by
      have : δ * (8192 / δ ^ 3) ≤ δ * M2 := mul_le_mul_of_nonneg_left
        (hM1.trans (by exact_mod_cast h12)) hδ.le
      have e : δ * (8192 / δ ^ 3) = 8192 / δ ^ 2 := by field_simp
      rw [e] at this
      rw [show 1024 / δ ^ 2 = (8192 / δ ^ 2) / 8 by ring]
      exact div_le_div_of_nonneg_right this (by norm_num)
    have : 1024 ≤ 1024 / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; have : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1; linarith
    linarith
  have hWlow : δ * M1 / 16 ≤ (W : ℝ) := by
    rw [hW]; push_cast
    refine le_min (by nlinarith) (le_trans ?_ hfl)
    have : (M1 : ℝ) ≤ M2 := by exact_mod_cast h12
    nlinarith
  have hW512 : 512 / δ ^ 2 ≤ (W : ℝ) := by
    rw [hW]; push_cast
    have h3 : 512 / δ ^ 2 ≤ 8192 / δ ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : δ ^ 3 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
      nlinarith [pow_pos hδ 2]
    refine le_min (h3.trans hM1) ?_
    have h4 := Nat.lt_floor_add_one (δ * M2 / 8)
    have h2 : 1024 / δ ^ 2 ≤ δ * M2 / 8 := by
      have : δ * (8192 / δ ^ 3) ≤ δ * M2 := mul_le_mul_of_nonneg_left
        (hM1.trans (by exact_mod_cast h12)) hδ.le
      have e : δ * (8192 / δ ^ 3) = 8192 / δ ^ 2 := by field_simp
      rw [e] at this
      rw [show 1024 / δ ^ 2 = (8192 / δ ^ 2) / 8 by ring]
      exact div_le_div_of_nonneg_right this (by norm_num)
    have : 1 ≤ 512 / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; have : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1; linarith
    have e : 1024 / δ ^ 2 = 2 * (512 / δ ^ 2) := by ring
    linarith
  have hW1 : 1 ≤ W := by
    have : (1 : ℝ) ≤ W := le_trans (by rw [le_div_iff₀ (by positivity)]; nlinarith) hW512
    exact_mod_cast this
  have hWM : W ≤ M1 := by rw [hW]; exact min_le_left _ _
  have hW8 : 8 * (1 / (δ * M2)) * W ≤ 1 := by
    have : (W : ℝ) ≤ δ * M2 / 8 := by
      rw [hW]; push_cast
      exact (min_le_right _ _).trans (Nat.floor_le (by positivity))
    rw [show 8 * (1 / (δ * M2)) * W = 8 * W / (δ * M2) by ring, div_le_one (by positivity)]
    linarith
  have hW128 : 128 ≤ (δ / 2) ^ 2 * W := by
    have : (δ / 2) ^ 2 * (512 / δ ^ 2) = 128 := by field_simp; norm_num
    rw [← this]; exact mul_le_mul_of_nonneg_left hW512 (by positivity)
  obtain ⟨k, hk1, hk2, hk3⟩ := vino hGsub (σ := δ / 2) (by positivity) (by linarith)
    hGcard hGb hW1 hWM hW8 hW128
  refine ⟨k, hk1, by rw [show 16 / δ = 8 / (δ / 2) by field_simp; norm_num]; exact hk2, ?_⟩
  refine hk3.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hWp : 0 < (W : ℝ) := by positivity
  have : δ ^ 4 * M1 * M2 ≤ 16 * (δ ^ 3 * M2 * W) := by
    have := mul_le_mul_of_nonneg_left hWlow (by positivity : (0 : ℝ) ≤ 16 * δ ^ 3 * M2)
    nlinarith
  field_simp
  nlinarith [pow_pos hδ 4, pow_pos hδ 3]

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

set_option maxHeartbeats 2000000 in
/-- The key step of Proposition 4.9: the bilinear coefficient `φ(x, y)` of two short
generators is close to a rational with small denominator. -/
lemma lq_pair {S : Finset (ZMod p)} {ρ1 ρ δ τ : ℝ} (hρ : 0 < ρ) (hρρ1 : ρ ≤ ρ1) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ : 200 * S.card * τ ≤ δ * ρ) (hS1 : 1 ≤ S.card)
    {φ : ZMod p → ZMod p → UnitAddCircle} {lam mu : ZMod p → UnitAddCircle}
    (hφ1 : ∀ m, snorm S m ≤ 2 * ρ1 → AddOn S (2 * ρ1) (fun n => φ n m))
    (hφ2 : ∀ n, snorm S n ≤ 2 * ρ1 → AddOn S (2 * ρ1) (fun m => φ n m))
    (hlam : AddOn S (2 * ρ1) lam) (hmu : AddOn S (2 * ρ1) mu)
    (hsum : δ ≤ ‖∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) * ec (φ n m + lam n + mu m)‖)
    {x y : ZMod p} {Mx My : ℕ} (hx : Mx * snorm S x ≤ τ) (hy : My * snorm S y ≤ τ)
    (hMx : 65536 / δ ^ 3 ≤ Mx) (hMy : 65536 / δ ^ 3 ≤ My) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 32 / δ ∧ ‖k • φ x y‖ ≤ 131072 / (δ ^ 4 * Mx * My) := by
  have hd1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS1
  have h65 : (1 : ℝ) ≤ 65536 / δ ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
    linarith
  have hMx1 : (1 : ℝ) ≤ Mx := h65.trans hMx
  have hMy1 : (1 : ℝ) ≤ My := h65.trans hMy
  have hτρ : τ ≤ ρ / 200 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 200)]
    nlinarith
  have hsx : snorm S x ≤ τ := le_trans (by nlinarith [snorm_nonneg (S := S) x]) hx
  have hsy : snorm S y ≤ τ := le_trans (by nlinarith [snorm_nonneg (S := S) y]) hy
  have hbx : ∀ b < Mx, snorm S ((b : ZMod p) * x) ≤ τ := fun b hb =>
    (snorm_nsmul_le b x).trans (le_trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hb.le) (snorm_nonneg _)) hx)
  have hby : ∀ b < My, snorm S ((b : ZMod p) * y) ≤ τ := fun b hb =>
    (snorm_nsmul_le b y).trans (le_trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hb.le) (snorm_nonneg _)) hy)
  have hbx' : ∀ b < Mx, (b : ℝ) * snorm S x ≤ τ := fun b hb =>
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hb.le) (snorm_nonneg _)) hx
  have hby' : ∀ b < My, (b : ℝ) * snorm S y ≤ τ := fun b hb =>
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hb.le) (snorm_nonneg _)) hy
  obtain ⟨F, hF⟩ : ∃ F : ZMod p → ZMod p → ℂ, F = fun n m => ec (φ n m + lam n + mu m) :=
    ⟨_, rfl⟩
  have hF1 : ∀ n m, ‖F n m‖ ≤ 1 := fun n m => by rw [hF]; simp
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℂ, X0 = ∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) * F n m :=
    ⟨_, rfl⟩
  have hX0δ : δ ≤ ‖X0‖ := by rw [hX0, hF]; exact hsum
  -- averaging over the shifts
  have hshift : ∀ b < Mx, ∀ b' < My, ‖(∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) *
      F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y)) - X0‖ ≤ δ / 2 := by
    intro b hb b' hb'
    rw [hX0]
    refine (shift2 (by linarith) hρ hτ0 (by linarith) (by linarith) (hbx b hb) (hby b' hb') F
      hF1).trans ?_
    have h1 : 50 * S.card * τ / ρ1 ≤ 50 * S.card * τ / ρ :=
      div_le_div_of_nonneg_left (by positivity) hρ hρρ1
    have h2 : 50 * S.card * τ / ρ ≤ δ / 4 := by
      rw [div_le_iff₀ hρ]; nlinarith
    linarith
  have hbig : δ / 2 * Mx * My ≤ ∑ n, ∑ m, regP S ρ1 n * regP S ρ m *
      ‖∑ b ∈ range Mx, ∑ b' ∈ range My, F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y)‖ := by
    have e : ∑ b ∈ range Mx, ∑ b' ∈ range My, (∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) *
        F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y)) =
        ∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) *
          ∑ b ∈ range Mx, ∑ b' ∈ range My, F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y) := by
      obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → ZMod p → ZMod p → ℂ, ∀ b b' n m, G b b' n m =
          (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) * F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y) :=
        ⟨_, fun _ _ _ _ => rfl⟩
      simp only [mul_sum, ← hG]
      calc ∑ b ∈ range Mx, ∑ b' ∈ range My, ∑ n, ∑ m, G b b' n m
          = ∑ b ∈ range Mx, ∑ n, ∑ m, ∑ b' ∈ range My, G b b' n m :=
            sum_congr rfl fun b _ => by rw [sum_comm]; exact sum_congr rfl fun n _ => sum_comm
        _ = ∑ n, ∑ m, ∑ b ∈ range Mx, ∑ b' ∈ range My, G b b' n m := by
            rw [sum_comm]; exact sum_congr rfl fun n _ => sum_comm
    have h1 : ‖∑ b ∈ range Mx, ∑ b' ∈ range My, (∑ n, ∑ m, (regP S ρ1 n : ℂ) *
        (regP S ρ m : ℂ) * F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y)) -
        (Mx * My : ℂ) * X0‖ ≤ Mx * My * (δ / 2) := by
      have e2 : (Mx * My : ℂ) * X0 = ∑ b ∈ range Mx, ∑ b' ∈ range My, X0 := by simp; ring
      rw [e2, ← sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ b ∈ range Mx, ∑ b' ∈ range My, δ / 2 := by
            refine sum_le_sum fun b hb => ?_
            rw [← sum_sub_distrib]
            refine (norm_sum_le _ _).trans (sum_le_sum fun b' hb' => ?_)
            exact hshift b (mem_range.1 hb) b' (mem_range.1 hb')
        _ = _ := by simp; ring
    have h2 : ‖(Mx * My : ℂ) * X0‖ = Mx * My * ‖X0‖ := by
      rw [norm_mul]; norm_cast
    rw [e] at h1
    have h3 := norm_sub_norm_le ((Mx * My : ℂ) * X0)
      (∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) *
          ∑ b ∈ range Mx, ∑ b' ∈ range My, F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y))
    rw [norm_sub_rev] at h3
    have h4 : ‖∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) *
          ∑ b ∈ range Mx, ∑ b' ∈ range My, F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y)‖ ≤
        ∑ n, ∑ m, regP S ρ1 n * regP S ρ m *
          ‖∑ b ∈ range Mx, ∑ b' ∈ range My, F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y)‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (regP_nonneg S n), abs_of_nonneg (regP_nonneg S m)]
    have hMM : (0 : ℝ) ≤ Mx * My := by positivity
    have := mul_le_mul_of_nonneg_left hX0δ hMM
    nlinarith
  obtain ⟨n, m, hn, hm, hnm⟩ := exists_pair_ge (by linarith) hρ.le _ hbig
  have hsn : snorm S n ≤ ρ1 := snorm_le_of_mem (mem_bohr_of_regP_ne_zero (by linarith) hn)
    (by linarith)
  have hsm : snorm S m ≤ ρ := snorm_le_of_mem (mem_bohr_of_regP_ne_zero hρ.le hm) hρ.le
  -- expansion of the phase
  have hexp : ∀ b < Mx, ∀ b' < My, F (n + (b : ZMod p) * x) (m + (b' : ZMod p) * y) =
      ec ((b * b') • φ x y + b • (φ x m + lam x) + b' • (φ n y + mu y) +
        (φ n m + lam n + mu m)) := by
    intro b hb b' hb'
    have h1 := hbx b hb; have h2 := hby b' hb'; have h3 := hbx' b hb; have h4 := hby' b' hb'
    have hmy : snorm S (m + (b' : ZMod p) * y) ≤ 2 * ρ1 :=
      (snorm_add_le _ _).trans (by linarith)
    rw [hF]; simp only
    congr 1
    have e1 := hφ1 _ hmy n ((b : ZMod p) * x) (by linarith)
    have e2 := (hφ1 _ hmy).map_nsmul b x (by linarith)
    have e3 := hφ2 n (by linarith) m ((b' : ZMod p) * y) (by linarith)
    have e4 := (hφ2 n (by linarith)).map_nsmul b' y (by linarith)
    have e5 := hφ2 x (by linarith) m ((b' : ZMod p) * y) (by linarith)
    have e6 := (hφ2 x (by linarith)).map_nsmul b' y (by linarith)
    have e7 := hlam n ((b : ZMod p) * x) (by linarith)
    have e8 := hlam.map_nsmul b x (by linarith)
    have e9 := hmu m ((b' : ZMod p) * y) (by linarith)
    have e10 := hmu.map_nsmul b' y (by linarith)
    (try simp only at e1 e2 e3 e4 e5 e6)
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, mul_nsmul']
    simp only [nsmul_add]
    abel
  have hbig2 : δ / 2 * Mx * My ≤ ‖∑ b ∈ range Mx, ∑ b' ∈ range My,
      ec ((b * b') • φ x y + b • (φ x m + lam x) + b' • (φ n y + mu y) +
        (φ n m + lam n + mu m))‖ := by
    refine hnm.trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun b hb => sum_congr rfl fun b' hb' => ?_
    exact hexp b (mem_range.1 hb) b' (mem_range.1 hb')
  have hδ2 : 0 < δ / 2 := by positivity
  have hM : 8192 / (δ / 2) ^ 3 = 65536 / δ ^ 3 := by field_simp; norm_num
  have hK : 8192 / ((δ / 2) ^ 4 * Mx * My) = 131072 / (δ ^ 4 * Mx * My) := by
    field_simp; norm_num
  have hK' : (16 : ℝ) / (δ / 2) = 32 / δ := by field_simp; norm_num
  rcases le_total Mx My with h | h
  · obtain ⟨k, hk1, hk2, hk3⟩ := bilin_major h hδ2 (by linarith) (by rw [hM]; exact hMx) _ _ _ _
      hbig2
    exact ⟨k, hk1, by rw [← hK']; exact hk2, by rw [← hK]; exact hk3⟩
  · have e : ∑ b ∈ range Mx, ∑ b' ∈ range My,
        ec ((b * b') • φ x y + b • (φ x m + lam x) + b' • (φ n y + mu y) +
          (φ n m + lam n + mu m)) = ∑ b' ∈ range My, ∑ b ∈ range Mx,
        ec ((b' * b) • φ x y + b' • (φ n y + mu y) + b • (φ x m + lam x) +
          (φ n m + lam n + mu m)) := by
      rw [sum_comm]
      refine sum_congr rfl fun b' _ => sum_congr rfl fun b _ => ?_
      rw [mul_comm b' b, add_right_comm ((b * b') • φ x y)]
    rw [e] at hbig2
    obtain ⟨k, hk1, hk2, hk3⟩ := bilin_major h hδ2 (by linarith) (by rw [hM]; exact hMy) _ _ _ _
      (by rw [mul_right_comm]; exact hbig2)
    exact ⟨k, hk1, by rw [← hK']; exact hk2, by rw [← hK, mul_right_comm]; exact hk3⟩

lemma half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff _ |>.2 hx
  linarith

set_option maxHeartbeats 4000000 in
/-- **Proposition 4.9** (large local quadratic exponential sums). -/
theorem large_quad (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) {ρ1 ρ δ : ℝ}
    (hρ : 0 < ρ) (hρρ1 : ρ ≤ ρ1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {φ : ZMod p → ZMod p → UnitAddCircle} {lam mu : ZMod p → UnitAddCircle}
    (hφ1 : ∀ m, snorm S m ≤ 2 * ρ1 → AddOn S (2 * ρ1) (fun n => φ n m))
    (hφ2 : ∀ n, snorm S n ≤ 2 * ρ1 → AddOn S (2 * ρ1) (fun m => φ n m))
    (hlam : AddOn S (2 * ρ1) lam) (hmu : AddOn S (2 * ρ1) mu)
    (hsum : δ ≤ ‖∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) * ec (φ n m + lam n + mu m)‖) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ (32 / δ) ^ (S.card ^ 2) ∧
      ∀ n m, snorm S n ≤ lqR S.card δ ρ → snorm S m ≤ lqR S.card δ ρ →
        ‖k • φ n m‖ ≤ lqK S.card δ ρ * snorm S n * snorm S m := by
  classical
  have hd1' : 1 ≤ S.card := by
    obtain ⟨s, hs, _⟩ := hS; exact card_pos.2 ⟨s, hs⟩
  obtain ⟨a, ℓ, hℓ, ha, hrep, -⟩ := bohr_basis hp hS
  generalize hd' : S.card = d at a ℓ hℓ ha hrep hd1' ⊢
  have hd : d = S.card := hd'.symm
  have hd1 : 1 ≤ d := hd1'
  have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = lqτ d δ ρ := ⟨_, rfl⟩
  have hτpos : 0 < τ := by rw [hτ, lqτ]; positivity
  have hτ200 : 200 * d * τ ≤ δ * ρ := by
    rw [hτ, lqτ]; rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hτρ : τ ≤ ρ := by
    rw [hτ, lqτ, div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨Mm, hMm⟩ : ∃ Mm : ℝ, Mm = 65536 / δ ^ 3 := ⟨_, rfl⟩
  have hMm1 : 1 ≤ Mm := by
    rw [hMm, le_div_iff₀ (by positivity)]
    have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
    linarith
  obtain ⟨M, hM⟩ : ∃ M : Fin d → ℕ, M = fun i => ⌊τ / ℓ i⌋₊ := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin d), I = univ.filter (fun i => Mm ≤ M i) := ⟨_, rfl⟩
  have hIM : ∀ i ∈ I, Mm ≤ M i := fun i hi => by rw [hI] at hi; exact (mem_filter.1 hi).2
  have hMτ : ∀ i, (M i : ℝ) * ℓ i ≤ τ := by
    intro i; rw [hM]; simp only
    have := Nat.floor_le (div_nonneg hτpos.le (hℓ i).le)
    rw [le_div_iff₀ (hℓ i)] at this; exact this
  have hMs : ∀ i, (M i : ℝ) * snorm S (a i) ≤ τ := fun i =>
    le_trans (mul_le_mul_of_nonneg_left (ha i) (Nat.cast_nonneg _)) (hMτ i)
  have hIℓ : ∀ i ∈ I, τ / 2 ≤ M i * ℓ i := by
    intro i hi
    have h1 : 1 ≤ τ / ℓ i := by
      have := hIM i hi; rw [hM] at this; (try simp only at this)
      have h2 : (⌊τ / ℓ i⌋₊ : ℝ) ≤ τ / ℓ i := Nat.floor_le (div_nonneg hτpos.le (hℓ i).le)
      linarith
    have := half_le_floor h1
    rw [hM]; simp only
    have e : τ / 2 = τ / ℓ i / 2 * ℓ i := by have := (hℓ i).ne'; field_simp
    rw [e]; exact mul_le_mul_of_nonneg_right this (hℓ i).le
  -- the pair step
  have hpair : ∀ ij : Fin d × Fin d, ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 32 / δ ∧
      (ij.1 ∈ I → ij.2 ∈ I → ‖k • φ (a ij.1) (a ij.2)‖ ≤
        131072 / (δ ^ 4 * M ij.1 * M ij.2)) := by
    intro ij
    by_cases h : ij.1 ∈ I ∧ ij.2 ∈ I
    · obtain ⟨k, hk1, hk2, hk3⟩ := lq_pair hρ hρρ1 hδ hδ1 hτpos.le (by rw [← hd]; exact hτ200)
        (by rw [← hd]; exact hd1) hφ1 hφ2 hlam hmu hsum (hMs ij.1) (hMs ij.2)
        (by rw [← hMm]; exact hIM _ h.1) (by rw [← hMm]; exact hIM _ h.2)
      exact ⟨k, hk1, hk2, fun _ _ => hk3⟩
    · refine ⟨1, le_rfl, ?_, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
      rw [Nat.cast_one, le_div_iff₀ hδ]; linarith
  choose kk hkk using hpair
  refine ⟨∏ ij, kk ij, ?_, ?_, ?_⟩
  · exact Finset.one_le_prod' fun ij _ => (hkk ij).1
  · push_cast
    calc ∏ ij, (kk ij : ℝ) ≤ ∏ _ij : Fin d × Fin d, (32 / δ) :=
          prod_le_prod (fun ij _ => by positivity) fun ij _ => (hkk ij).2.1
      _ = (32 / δ) ^ (d ^ 2) := by
            rw [prod_const, card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  · intro n m hn hm
    have hK32 : (1 : ℝ) ≤ 32 / δ := by rw [le_div_iff₀ hδ]; linarith
    -- bound for the coefficients `φ(a_i, a_j)`
    have hcoef : ∀ i ∈ I, ∀ j ∈ I, ‖(∏ ij, kk ij) • φ (a i) (a j)‖ ≤
        (32 / δ) ^ (d ^ 2) * (131072 / (δ ^ 4 * M i * M j)) := by
      intro i hi j hj
      rw [← Finset.mul_prod_erase univ kk (mem_univ (i, j)), mul_nsmul]
      refine norm_nsmul_le.trans ?_
      have hrest : ((∏ x ∈ univ.erase (i, j), kk x : ℕ) : ℝ) ≤ (32 / δ) ^ (d ^ 2) := by
        push_cast
        calc ∏ x ∈ univ.erase (i, j), (kk x : ℝ) ≤ ∏ x ∈ univ.erase (i, j), (32 / δ) :=
              prod_le_prod (fun ij _ => by positivity) fun ij _ => (hkk ij).2.1
          _ = (32 / δ) ^ ((univ.erase (i, j)).card) := prod_const _
          _ ≤ (32 / δ) ^ (d ^ 2) := pow_le_pow_right₀ hK32 (by
            rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_prod, Fintype.card_fin, sq]
            omega)
      exact mul_le_mul hrest ((hkk (i, j)).2.2 hi hj) (norm_nonneg _) (by positivity)
    -- representations of `n` and `m`
    obtain ⟨cn, hcn, hcnb⟩ := hrep n
    obtain ⟨cm, hcm, hcmb⟩ := hrep m
    have hRdef : lqR d δ ρ = τ / (2 ^ (d ^ 2) * d * (Mm + 1)) := by rw [lqR, hτ, hMm]
    have hKd : (0 : ℝ) < 2 ^ (d ^ 2) * d := by positivity
    have hzero : ∀ (x : ZMod p) (c : Fin d → ℤ), snorm S x ≤ lqR d δ ρ →
        (∀ i, |(c i : ℝ)| * ℓ i ≤ 2 ^ (d ^ 2) * (d * snorm S x)) → ∀ i ∉ I, c i = 0 := by
      intro x c hx hc i hi
      have h1 : ¬ Mm ≤ M i := fun h => hi (by rw [hI]; exact mem_filter.2 ⟨mem_univ _, h⟩)
      push_neg at h1
      have h2 : τ / ℓ i < Mm + 1 := by
        have := Nat.lt_floor_add_one (τ / ℓ i)
        rw [hM] at h1; (try simp only at h1); linarith
      have h3 : τ < (Mm + 1) * ℓ i := by rwa [div_lt_iff₀ (hℓ i)] at h2
      have h4 : |(c i : ℝ)| * ℓ i < ℓ i := by
        refine lt_of_le_of_lt (hc i) ?_
        have : 2 ^ (d ^ 2) * (d * snorm S x) ≤ τ / (Mm + 1) := by
          rw [hRdef] at hx
          rw [le_div_iff₀ (by positivity)]
          rw [le_div_iff₀ (by positivity)] at hx
          nlinarith
        refine lt_of_le_of_lt this ?_
        rw [div_lt_iff₀ (by positivity)]; linarith
      have h5 : |(c i : ℝ)| < 1 := by
        have := hℓ i
        nlinarith
      have : |c i| < 1 := by exact_mod_cast h5
      exact Int.abs_lt_one_iff.1 this
    have hn0 := hzero n cn hn hcnb
    have hm0 := hzero m cm hm hcmb
    have hR0 : 0 ≤ lqR d δ ρ := le_trans (snorm_nonneg _) hn
    have hRτ : 2 ^ (d ^ 2) * (d * lqR d δ ρ) ≤ τ := by
      rw [hRdef]
      have e : 2 ^ (d ^ 2) * (d * (τ / (2 ^ (d ^ 2) * d * (Mm + 1)))) = τ / (Mm + 1) := by
        field_simp
      rw [e, div_le_iff₀ (by positivity)]; nlinarith
    have hsumc : ∀ (x : ZMod p) (c : Fin d → ℤ), snorm S x ≤ lqR d δ ρ →
        (∀ i, |(c i : ℝ)| * ℓ i ≤ 2 ^ (d ^ 2) * (d * snorm S x)) →
        ∑ i, |(c i : ℝ)| * snorm S (a i) ≤ d * τ := by
      intro x c hx hc
      calc ∑ i, |(c i : ℝ)| * snorm S (a i) ≤ ∑ _i : Fin d, τ := by
            refine sum_le_sum fun i _ => ?_
            refine le_trans (mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _)) ?_
            refine (hc i).trans (le_trans ?_ hRτ)
            gcongr
        _ = d * τ := by simp
    have hdτ : (d : ℝ) * τ ≤ ρ / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]; nlinarith
    have hRle : lqR d δ ρ ≤ τ := by
      rw [hRdef]
      refine div_le_self hτpos.le ?_
      have h2 : (1 : ℝ) ≤ 2 ^ (d ^ 2) := one_le_pow₀ (by norm_num)
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h2 hd1r)
        (by linarith)
    have hsn : snorm S n ≤ τ := hn.trans hRle
    have hsm : snorm S m ≤ τ := hm.trans hRle
    -- bilinear expansion
    have hexp : φ n m = ∑ i, ∑ j, (cn i * cm j) • φ (a i) (a j) := by
      have e1 : φ n m = ∑ i, cn i • φ (a i) m := by
        have := (hφ1 m (by linarith)).map_sum univ cn a (by
          have := hsumc n cn hn hcnb; linarith)
        rw [← hcn] at this; exact this
      rw [e1]
      refine sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ I
      · have hai : snorm S (a i) ≤ τ := by
          have h1 := hMs i; have h2 := hIM i hi
          have : (1 : ℝ) ≤ M i := hMm1.trans h2
          nlinarith [snorm_nonneg (S := S) (a i)]
        have := (hφ2 (a i) (by linarith)).map_sum univ cm a (by
          have := hsumc m cm hm hcmb; linarith)
        rw [← hcm] at this
        try dsimp only at this
        rw [this, smul_sum]
        exact sum_congr rfl fun j _ => by rw [mul_smul]
      · simp [hn0 i hi]
    rw [hexp, smul_sum]
    refine (norm_sum_le _ _).trans ?_
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (2 * (2 ^ (d ^ 2) * d) * snorm S n / τ) *
        (2 * (2 ^ (d ^ 2) * d) * snorm S m / τ) * (32 / δ) ^ (d ^ 2) * (131072 / δ ^ 4) :=
      ⟨_, rfl⟩
    have hterm : ∀ i j, ‖(∏ ij, kk ij) • ((cn i * cm j) • φ (a i) (a j))‖ ≤ B := by
      intro i j
      have hB0 : 0 ≤ B := by rw [hB]; have := snorm_nonneg (S := S) n;
                             have := snorm_nonneg (S := S) m; positivity
      by_cases hij : i ∈ I ∧ j ∈ I
      · rw [smul_comm]
        refine (norm_zsmul_le _ _).trans ?_
        have hc := hcoef i hij.1 j hij.2
        have hMi : τ / 2 ≤ M i * ℓ i := hIℓ i hij.1
        have hMj : τ / 2 ≤ M j * ℓ j := hIℓ j hij.2
        have hMi0 : (0 : ℝ) < M i := by
          have := hIM i hij.1; linarith
        have hMj0 : (0 : ℝ) < M j := by
          have := hIM j hij.2; linarith
        have hni : |(cn i : ℝ)| / M i ≤ 2 * (2 ^ (d ^ 2) * d) * snorm S n / τ := by
          rw [div_le_div_iff₀ hMi0 hτpos]
          have h1 := hcnb i
          have h2 := hℓ i
          nlinarith [abs_nonneg (cn i : ℝ), snorm_nonneg (S := S) n]
        have hmj : |(cm j : ℝ)| / M j ≤ 2 * (2 ^ (d ^ 2) * d) * snorm S m / τ := by
          rw [div_le_div_iff₀ hMj0 hτpos]
          have h1 := hcmb j
          have h2 := hℓ j
          nlinarith [abs_nonneg (cm j : ℝ), snorm_nonneg (S := S) m]
        rw [Int.norm_eq_abs, Int.cast_mul, abs_mul]
        calc |(cn i : ℝ)| * |(cm j : ℝ)| * ‖(∏ ij, kk ij) • φ (a i) (a j)‖
            ≤ |(cn i : ℝ)| * |(cm j : ℝ)| * ((32 / δ) ^ (d ^ 2) * (131072 / (δ ^ 4 * M i * M j))) :=
              mul_le_mul_of_nonneg_left hc (by positivity)
          _ = (|(cn i : ℝ)| / M i) * (|(cm j : ℝ)| / M j) * (32 / δ) ^ (d ^ 2) *
                (131072 / δ ^ 4) := by field_simp
          _ ≤ B := by
              rw [hB]
              have h0 : 0 ≤ |(cn i : ℝ)| / M i := by positivity
              have h0' : 0 ≤ |(cm j : ℝ)| / M j := by positivity
              have := mul_le_mul hni hmj h0' (le_trans h0 hni)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity))
                (by positivity)
      · have : cn i * cm j = 0 := by
          rcases not_and_or.1 hij with h | h
          · rw [hn0 i h, zero_mul]
          · rw [hm0 j h, mul_zero]
        rw [this, zero_smul, smul_zero, norm_zero]; exact hB0
    calc ∑ i, ‖(∏ ij, kk ij) • ∑ j, (cn i * cm j) • φ (a i) (a j)‖
        ≤ ∑ _i : Fin d, ∑ _j : Fin d, B :=
          sum_le_sum fun i _ => by
            rw [smul_sum]; exact (norm_sum_le _ _).trans (sum_le_sum fun j _ => hterm i j)
      _ = d ^ 2 * B := by simp; ring
      _ = lqK d δ ρ * snorm S n * snorm S m := by
          rw [hB, lqK, ← hτ]; ring

end

end GT
end File_GT_LargeQuad

open Finset KM
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)} (hS : ∃ s ∈ S, s ≠ 0) {ρ1 ρ δ : ℝ}
    (hρ : 0 < ρ) (hρρ1 : ρ ≤ ρ1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {φ : ZMod p → ZMod p → UnitAddCircle} {lam mu : ZMod p → UnitAddCircle}
    (hφ1 : ∀ m, snorm S m ≤ 2 * ρ1 → AddOn S (2 * ρ1) (fun n => φ n m))
    (hφ2 : ∀ n, snorm S n ≤ 2 * ρ1 → AddOn S (2 * ρ1) (fun m => φ n m))
    (hlam : AddOn S (2 * ρ1) lam) (hmu : AddOn S (2 * ρ1) mu)
    (hsum : δ ≤ ‖∑ n, ∑ m, (regP S ρ1 n : ℂ) * (regP S ρ m : ℂ) * ec (φ n m + lam n + mu m)‖) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ (32 / δ) ^ (S.card ^ 2) ∧
      ∀ n m, snorm S n ≤ lqR S.card δ ρ → snorm S m ≤ lqR S.card δ ρ →
        ‖k • φ n m‖ ≤ lqK S.card δ ρ * snorm S n * snorm S m :=
  @GT.large_quad p _ hp S hS ρ1 ρ δ hρ hρρ1 hδ hδ1 φ lam mu hφ1 hφ2 hlam hmu hsum

