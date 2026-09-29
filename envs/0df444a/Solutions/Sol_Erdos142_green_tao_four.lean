-- Prove2me | solution 1 for Erdos142.green_tao_four
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:53.507068+00:00
-- url     : https://prove2.me/submissions/1baaccf3-693d-49a7-992f-5dbba4d9036a

import Mathlib
import Definitions.Def_Erdos142Basic
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_bad_dim_thm
import Theorems.Thm_GT_bad_ed_thm

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

@[simp] lemma cn_zero : cn (0 : ZMod N) = 0 := by simp [cn]

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

lemma bohr_mono (h : ρ ≤ ρ') : bohr Γ ρ ⊆ bohr Γ ρ' := by
  intro x hx
  rw [mem_bohr] at *
  exact fun γ hγ => (hx γ hγ).trans h

lemma bohr_eq_univ (h : 1 / 2 ≤ ρ) : bohr Γ ρ = univ := by
  ext x; simp only [mem_bohr, mem_univ, iff_true]
  exact fun γ _ => (cn_le_half _).trans h

lemma bohr_nonempty (hρ : 0 ≤ ρ) : (bohr Γ ρ).Nonempty := ⟨0, zero_mem_bohr hρ⟩

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

lemma sum_sub_right (f : G → ℝ) (t : G) : ∑ x, f (x - t) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.subRight t) _ _ (fun _ => rfl)

lemma sum_sub_left (f : G → ℝ) (t : G) : ∑ x, f (t - x) = ∑ x, f x :=
  Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.addLeft t)) _ _
    (fun x => by simp [sub_eq_add_neg])

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

end

end GT
end File_GT_Bohr

section File_GT_Torus
/-!
# Tori and locally quadratic maps (Green–Tao §4, §5)

Green–Tao work with *dilated tori* `∏ ℝ/λ_i ℤ`.  Since the orthogonal complement of a dual
frequency in a dilated torus is not itself a dilated torus (their Theorem 5.1 handles this by a
bilipschitz reparametrisation), we instead work with the slightly more general class of tori
`ℝ^d / Γ`, where `Γ` is a lattice with a given basis, isometrically embedded in a Euclidean
space.  Concretely a torus `G` is given by vectors `v_1, …, v_d` of `ℝ^n`; its points are
`(ℝ/ℤ)^d`, the point with coordinates `t` corresponds to `∑ t_i v_i` modulo the lattice
`Γ = ⊕ ℤ v_i`, and the metric is the quotient Euclidean metric.  The volume is the covolume of
`Γ`, i.e. the square root of the Gram determinant of the `v_i`.  Dilated tori are the case of
orthogonal `v_i` with `‖v_i‖ = λ_i`.
-/

namespace GT

noncomputable section

open Finset

namespace DTorus

lemma point_vol : point.vol = 1 := Fintype.prod_empty _

lemma point_good : point.Good := by
  refine ⟨linearIndependent_empty_type, fun m hm => absurd (funext fun i => Fin.elim0 i) hm, ?_⟩
  rw [Fintype.prod_empty, one_pow]
  show (1 : ℝ) ≤ 2 ^ (point.d ^ 2) * (Matrix.gram ℝ point.v).det
  rw [Matrix.det_isEmpty, mul_one]
  exact one_le_pow₀ (by norm_num)

lemma point_isLip (F : point.Pt → ℝ) : point.IsLip F := by
  intro t t'
  have : point.pt t = point.pt t' := funext fun i => Fin.elim0 i
  rw [this, sub_self, abs_zero]
  exact norm_nonneg _

end DTorus

end

end GT
end File_GT_Torus

section File_GT_Khint
/-!
# Khintchine-type recurrence for four-term progressions (Green–Tao 2017, Theorem 3.1)

A joint distribution of a pair of random variables `(a, r)` in `ZMod p` is encoded as a weight
function `w : ZMod p × ZMod p → ℝ` that is non-negative and sums to one.
-/

open Finset

namespace GT

noncomputable section

/-- The weighted count of four-term progressions `Λ_{a,r}(f) = E f(a) f(a+r) f(a+2r) f(a+3r)`,
for the joint distribution `w` of `(a, r)`. -/
def lam4 {p : ℕ} [NeZero p] (w : ZMod p × ZMod p → ℝ) (f : ZMod p → ℝ) : ℝ :=
  ∑ z, w z * (f z.1 * f (z.1 + z.2) * f (z.1 + 2 * z.2) * f (z.1 + 3 * z.2))

/-- **Khintchine-type recurrence with thick differences** (Green–Tao, Theorem 3.1, for
`[0,1]`-valued `f`; the approximations `E f(a) = E f + O(η)` and `Λ ≥ (E f(a))^4 - O(η)` are
combined into the single bound `Λ ≥ (E f)^4 - O(η)`). -/
def KhintProp : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (p : ℕ) [NeZero p], p.Prime → ∀ η : ℝ, 0 < η → η ≤ 1 / 10 →
    ∀ f : ZMod p → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      ∃ w : ZMod p × ZMod p → ℝ, (∀ z, 0 ≤ w z) ∧ ∑ z, w z = 1 ∧
        (∑ x, f x / p) ^ 4 - C * η ≤ lam4 w f ∧
        ∑ a, w (a, 0) ≤ Real.exp ((1 / η) ^ C) / p

end

end GT
end File_GT_Khint

section File_GT_Iter
/-!
# The energy/dimension iteration (Green–Tao, end of §3)

A *random triple* `(a, r, 𝐟)` in which `𝐟` becomes deterministic after conditioning on a
finite label `c` is encoded by `Triple p`: a finite label type with a probability vector `π`,
for each label a joint law `w c` of `(a, r)`, and a function `F c`.

`MainAbstract C₂ C₅` is Proposition 3.3 of Green–Tao (with the path-length bound `64 η^{-2C₂}`
and the thickness bound `exp(η^{-C₅})/p`), and `khint_of_mainAbstract` deduces Theorem 3.1.
-/

open Finset

namespace GT

noncomputable section

namespace Triple

variable {p : ℕ} [NeZero p] (t : Triple p) (f : ZMod p → ℝ)

/-- Validity: probability vectors, and `𝐟` is `1`-bounded. -/
def Valid : Prop :=
  (∀ c, 0 ≤ t.π c) ∧ ∑ c, t.π c = 1 ∧ (∀ c z, 0 ≤ t.w c z) ∧ (∀ c, ∑ z, t.w c z = 1) ∧
    ∀ c x, |t.F c x| ≤ 1

/-- `P(r = 0)`. -/
def pzero : ℝ := ∑ c, t.π c * ∑ a, t.w c (a, 0)

/-- The (unconditioned) joint law of `(a, r)`. -/
def law (z : ZMod p × ZMod p) : ℝ := ∑ c, t.π c * t.w c z

end Triple

/-- Paths of length `k` from `v₀` in a directed graph. -/
inductive Reach {V : Type*} (E : V → V → Prop) (v₀ : V) : ℕ → V → Prop
  | zero : Reach E v₀ 0 v₀
  | step {k : ℕ} {v v' : V} : Reach E v₀ k v → E v v' → Reach E v₀ (k + 1) v'

/-- **Proposition 3.3** (abstract main proposition). -/
def MainAbstract (C₂ C₅ : ℕ) : Prop :=
  ∀ (p : ℕ) [NeZero p], p.Prime → ∀ η : ℝ, 0 < η → η ≤ 1 / 10 →
    Real.exp ((1 / η) ^ (3 * C₅)) ≤ p →
    ∀ f : ZMod p → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    ∃ (V : Type 1) (E : V → V → Prop) (t : V → Triple p) (d₂ d₂p : V → ℕ) (v₀ : V),
      d₂ v₀ = 0 ∧ (∀ v, d₂p v ≤ d₂ v) ∧
      ∀ k v, Reach E v₀ k v → (k : ℝ) ≤ 64 * (1 / η) ^ (2 * C₂) →
        (t v).Valid ∧
        (t v).pzero ≤ Real.exp ((1 / η) ^ C₅) / p ∧
        |(t v).ex f - ∑ x, f x / p| ≤ η ∧
        ((η < |(t v).exF - (t v).ex f| ∨ η < |(t v).lamF - (t v).lam f|) →
          ∃ v', E v v' ∧ (t v').energy f ≤ (t v).energy f - η ^ C₂ ∧ d₂ v' ≤ d₂ v + 1) ∧
        ((t v).lamF ≤ (t v).exF ^ 4 - η →
          ∃ v', E v v' ∧ (t v').energy f ≤ (t v).energy f + η ^ (3 * C₂) ∧
            d₂ v' ≤ d₂ v ∧ d₂p v' + 1 ≤ d₂p v)

namespace Triple

variable {p : ℕ} [NeZero p] {t : Triple p} {f : ZMod p → ℝ}

lemma law_nonneg (ht : t.Valid) (z : ZMod p × ZMod p) : 0 ≤ t.law z :=
  Finset.sum_nonneg fun c _ => mul_nonneg (ht.1 c) (ht.2.2.1 c z)

lemma sum_law (ht : t.Valid) : ∑ z, t.law z = 1 := by
  unfold law
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ht.2.2.2.1, mul_one, ht.2.1]

lemma lam4_law : lam4 t.law f = t.lam f := by
  unfold lam4 lam law
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun z _ => by ring

lemma sum_law_zero : ∑ a, t.law (a, 0) = t.pzero := by
  unfold law pzero
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

lemma energy_nonneg (ht : t.Valid) : 0 ≤ t.energy f :=
  Finset.sum_nonneg fun c _ => mul_nonneg (ht.1 c)
    (Finset.sum_nonneg fun z _ => mul_nonneg (ht.2.2.1 c z) (sq_nonneg _))

lemma energy_le_four (ht : t.Valid) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : t.energy f ≤ 4 := by
  have hb : ∀ c z, t.w c z * (f z.1 - t.F c z.1) ^ 2 ≤ t.w c z * 4 := by
    intro c z
    apply mul_le_mul_of_nonneg_left _ (ht.2.2.1 c z)
    have h1 := hf z.1
    have h2 := abs_le.mp (ht.2.2.2.2 c z.1)
    nlinarith
  calc t.energy f ≤ ∑ c, t.π c * ∑ z, t.w c z * 4 :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun z _ => hb c z) (ht.1 c)
    _ = 4 := by
        simp_rw [← Finset.sum_mul, ht.2.2.2.1, one_mul, ← Finset.sum_mul, ht.2.1, one_mul]

end Triple

/-- `(E f)^4 ≤ E f^4`. -/
lemma mean_pow_four_le {p : ℕ} [NeZero p] (f : ZMod p → ℝ) :
    (∑ x, f x / p) ^ 4 ≤ ∑ x, f x ^ 4 / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
  -- Cauchy–Schwarz twice
  have cs : ∀ g : ZMod p → ℝ, (∑ x, g x / p) ^ 2 ≤ ∑ x, g x ^ 2 / p := by
    intro g
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod p))) (f := g)
    rw [hcard] at h2
    rw [← Finset.sum_div, ← Finset.sum_div, div_pow, div_le_div_iff₀ (by positivity) hp]
    calc (∑ x, g x) ^ 2 * p ≤ (p * ∑ x, g x ^ 2) * p := by gcongr
      _ = (∑ x, g x ^ 2) * p ^ 2 := by ring
  have h1 := cs f
  have h2 := cs (fun x => f x ^ 2)
  simp only [← pow_mul] at h2
  calc (∑ x, f x / p) ^ 4 = ((∑ x, f x / p) ^ 2) ^ 2 := by ring
    _ ≤ (∑ x, f x ^ 2 / p) ^ 2 := by
        apply pow_le_pow_left₀ (sq_nonneg _) h1
    _ ≤ ∑ x, f x ^ 4 / p := h2

/-- The good case: a triple with all errors small gives the conclusion of Theorem 3.1. -/
lemma khint_of_good {p : ℕ} [NeZero p] {t : Triple p} {f : ZMod p → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {η : ℝ} (hη : 0 ≤ η)
    (hw : |t.ex f - ∑ x, f x / p| ≤ η) (h1 : |t.exF - t.ex f| ≤ η)
    (h4 : |t.lamF - t.lam f| ≤ η) (hlow : t.exF ^ 4 - η < t.lamF) :
    (∑ x, f x / p) ^ 4 - 10 * η ≤ lam4 t.law f := by
  rw [Triple.lam4_law]
  set x := ∑ x, f x / p with hx
  set y := t.exF
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hx0 : 0 ≤ x := Finset.sum_nonneg fun a _ => div_nonneg (hf a).1 hp.le
  have hx1 : x ≤ 1 := by
    have hcard : (Finset.univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
    calc x ≤ ∑ _a : ZMod p, 1 / (p : ℝ) :=
          Finset.sum_le_sum fun a _ => div_le_div_of_nonneg_right (hf a).2 hp.le
      _ = 1 := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; field_simp
  have hy : x - 2 * η ≤ y := by
    have := abs_le.mp hw; have := abs_le.mp h1; linarith
  have hy4 : x ^ 4 - 8 * η ≤ y ^ 4 := by
    rcases le_or_gt (x - 2 * η) 0 with hneg | hpos
    · have : x ^ 4 ≤ x := by
        calc x ^ 4 ≤ x ^ 1 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
          _ = x := pow_one x
      nlinarith [pow_two_nonneg (y ^ 2)]
    · have hyy : (x - 2 * η) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hpos.le hy 4
      have : x ^ 4 - (x - 2 * η) ^ 4 ≤ 8 * η := by
        have e : x ^ 4 - (x - 2 * η) ^ 4 =
            2 * η * (x ^ 3 + x ^ 2 * (x - 2 * η) + x * (x - 2 * η) ^ 2 + (x - 2 * η) ^ 3) := by
          ring
        rw [e]
        have hb : x ^ 3 + x ^ 2 * (x - 2 * η) + x * (x - 2 * η) ^ 2 + (x - 2 * η) ^ 3 ≤ 4 := by
          have a1 : x - 2 * η ≤ 1 := by linarith
          have b1 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
          have b2 : x ^ 2 * (x - 2 * η) ≤ 1 :=
            mul_le_one₀ (pow_le_one₀ hx0 hx1) hpos.le a1
          have b3 : x * (x - 2 * η) ^ 2 ≤ 1 :=
            mul_le_one₀ hx1 (sq_nonneg _) (pow_le_one₀ hpos.le a1)
          have b4 : (x - 2 * η) ^ 3 ≤ 1 := pow_le_one₀ hpos.le a1
          linarith
        have := mul_le_mul_of_nonneg_left hb (by linarith : (0:ℝ) ≤ 2 * η)
        linarith
      linarith
  have := abs_le.mp h4
  linarith

/-- The final counting step of the iteration. -/
lemma iteration_count {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {C₂ : ℕ} (hC₂ : 2 ≤ C₂)
    {E₀ E₁ : ℝ} (hE₀ : E₀ ≤ 4) (hE₁ : 0 ≤ E₁) {e D d : ℕ}
    (hen : E₁ ≤ E₀ - e * η ^ C₂ + D * η ^ (3 * C₂)) (hpot : 2 * (D + d) ≤ e * (e + 1))
    (hK : 64 * (1 / η) ^ (2 * C₂) - 1 ≤ (e + D : ℝ)) (hK' : (e + D : ℝ) ≤ 64 * (1 / η) ^ (2 * C₂)) :
    False := by
  set u : ℝ := (1 / η) ^ C₂ with hu
  have h10 : 10 ≤ 1 / η := by rw [le_div_iff₀ hη0]; linarith
  have hu100 : 100 ≤ u := by
    calc (100 : ℝ) = 10 ^ 2 := by norm_num
      _ ≤ (1 / η) ^ 2 := pow_le_pow_left₀ (by norm_num) h10 2
      _ ≤ u := pow_le_pow_right₀ (by linarith) hC₂
  have hu0 : 0 < u := by linarith
  have e1 : η ^ C₂ = 1 / u := by rw [hu, one_div_pow, one_div_one_div]
  have e3 : η ^ (3 * C₂) = 1 / u ^ 3 := by rw [pow_mul', e1]; ring
  have e2 : (1 / η) ^ (2 * C₂) = u ^ 2 := by rw [pow_mul']
  rw [e1, e3] at hen
  rw [e2] at hK hK'
  have hD : (D : ℝ) ≤ 64 * u ^ 2 := by
    have : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    linarith
  have hDu : (D : ℝ) * (1 / u ^ 3) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    nlinarith
  have he : (e : ℝ) ≤ 5 * u := by
    have : (e : ℝ) * (1 / u) ≤ 5 := by linarith
    rw [mul_one_div, div_le_iff₀ hu0] at this
    linarith
  have hpot' : 2 * (D : ℝ) ≤ e * (e + 1) := by
    have : ((2 * (D + d) : ℕ) : ℝ) ≤ ((e * (e + 1) : ℕ) : ℝ) := by exact_mod_cast hpot
    push_cast at this
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have : (e : ℝ) * (e + 1) ≤ 5 * u * (5 * u + 1) :=
    mul_le_mul he (by linarith) (by linarith) (by linarith)
  nlinarith

theorem khint_of_mainAbstract {C₂ C₅ : ℕ} (hC₂ : 2 ≤ C₂) (h : MainAbstract C₂ C₅) :
    KhintProp := by
  refine ⟨10 + 3 * C₅, by omega, ?_⟩
  intro p _ hp η hη0 hη1 f hf
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hη1' : 1 ≤ 1 / η := by rw [le_div_iff₀ hη0]; linarith
  have hexp_mono : ∀ m n : ℕ, m ≤ n → Real.exp ((1 / η) ^ m) ≤ Real.exp ((1 / η) ^ n) :=
    fun m n hmn => Real.exp_le_exp.mpr (pow_le_pow_right₀ hη1' hmn)
  have hCη : 10 * η ≤ ((10 + 3 * C₅ : ℕ) : ℝ) * η := by
    apply mul_le_mul_of_nonneg_right _ hη0.le
    push_cast
    have : (0 : ℝ) ≤ C₅ := Nat.cast_nonneg _
    linarith
  by_cases hsmall : Real.exp ((1 / η) ^ (3 * C₅)) ≤ p
  swap
  · -- small `p`: take `a` uniform and `r = 0`
    push_neg at hsmall
    refine ⟨fun z => if z.2 = 0 then 1 / p else 0, fun z => by (try dsimp only); split_ifs <;> positivity,
      ?_, ?_, ?_⟩
    · rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul]
      field_simp
    · have e : lam4 (fun z : ZMod p × ZMod p => if z.2 = 0 then 1 / (p : ℝ) else 0) f =
          ∑ x, f x ^ 4 / p := by
        unfold lam4
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single (0 : ZMod p)]
        · simp only [if_true, mul_zero, add_zero]; ring
        · intro b _ hb; simp [hb]
        · simp
      rw [e]
      have := mean_pow_four_le f
      have : (0 : ℝ) ≤ ((10 + 3 * C₅ : ℕ) : ℝ) * η := by positivity
      linarith
    · simp only [if_true, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [mul_one_div, div_self hp0.ne', le_div_iff₀ hp0, one_mul]
      exact hsmall.le.trans (hexp_mono _ _ (by omega))
  · obtain ⟨V, E, t, d₂, d₂p, v₀, hd0, hdp, H⟩ := h p hp η hη0 hη1 hsmall f hf
    by_contra hno
    have hbad : ∀ k v, Reach E v₀ k v → (k : ℝ) ≤ 64 * (1 / η) ^ (2 * C₂) →
        (η < |(t v).exF - (t v).ex f| ∨ η < |(t v).lamF - (t v).lam f|) ∨
          (t v).lamF ≤ (t v).exF ^ 4 - η := by
      intro k v hr hk
      obtain ⟨hv, hth, hw, -, -⟩ := H k v hr hk
      by_contra hgood
      push_neg at hgood
      obtain ⟨⟨g1, g2⟩, g3⟩ := hgood
      apply hno
      refine ⟨(t v).law, Triple.law_nonneg hv, Triple.sum_law hv, ?_, ?_⟩
      · have := khint_of_good hf hη0.le hw g1 g2 g3
        linarith
      · rw [Triple.sum_law_zero]
        exact hth.trans (div_le_div_of_nonneg_right (hexp_mono _ _ (by omega)) hp0.le)
    set K := ⌊64 * (1 / η) ^ (2 * C₂)⌋₊ with hKdef
    have hKle : (K : ℝ) ≤ 64 * (1 / η) ^ (2 * C₂) := Nat.floor_le (by positivity)
    have hKge : 64 * (1 / η) ^ (2 * C₂) - 1 ≤ (K : ℝ) := by
      have := Nat.lt_floor_add_one (64 * (1 / η) ^ (2 * C₂)); linarith
    have claim : ∀ k, k ≤ K → ∃ (v : V) (e D : ℕ), Reach E v₀ k v ∧ e + D = k ∧
        (t v).energy f ≤ (t v₀).energy f - e * η ^ C₂ + D * η ^ (3 * C₂) ∧ d₂ v ≤ e ∧
        2 * (D + d₂p v) ≤ e * (e + 1) := by
      intro k
      induction k with
      | zero =>
        intro _
        have := hdp v₀
        rw [hd0] at this
        exact ⟨v₀, 0, 0, Reach.zero, rfl, by simp, by simp [hd0], by omega⟩
      | succ k ih =>
        intro hk
        obtain ⟨v, e, D, hr, hsum, hen, hd2, hpot⟩ := ih (by omega)
        have hkK : (k : ℝ) ≤ 64 * (1 / η) ^ (2 * C₂) :=
          (Nat.cast_le.mpr (by omega : k ≤ K)).trans hKle
        obtain ⟨-, -, -, hE, hD⟩ := H k v hr hkK
        rcases hbad k v hr hkK with hb | hb
        · obtain ⟨v', hvv', hen', hd'⟩ := hE hb
          refine ⟨v', e + 1, D, hr.step hvv', by omega, ?_, by omega, ?_⟩
          · push_cast; linarith
          · have := hdp v'
            have : d₂p v' ≤ e + 1 := by omega
            nlinarith
        · obtain ⟨v', hvv', hen', hd', hdp'⟩ := hD hb
          refine ⟨v', e, D + 1, hr.step hvv', by omega, ?_, by omega, by omega⟩
          push_cast; linarith
    obtain ⟨v, e, D, hr, hsum, hen, -, hpot⟩ := claim K le_rfl
    have hv := (H K v hr hKle).1
    have hv0 := (H 0 v₀ Reach.zero (by rw [Nat.cast_zero]; positivity)).1
    have hsumr : (e + D : ℝ) = K := by exact_mod_cast hsum
    exact iteration_count hη0 hη1 hC₂ (Triple.energy_le_four hv0 hf) (Triple.energy_nonneg hv)
      hen hpot (by rw [hsumr]; exact hKge) (by rw [hsumr]; exact hKle)

end

end GT
end File_GT_Iter

section File_GT_BadEdA
/-!
# Theorem 6.6, the linear case: shifting the approximant by a constant

If `|E 𝐟(a) - E f(a)| > η`, adding the constant `±η/2` to every `F_c` (and truncating to
`[-1, 1]`) decreases the energy by at least `η²/2`, without changing any of the other data.
-/

open Finset KM

namespace GT

noncomputable section

namespace SLA

variable {p : ℕ} [NeZero p]

/-- The triple of a valid approximant is valid. -/
lemma triple_valid {v : SLA p} (hv : v.Valid) (η : ℝ) : (v.triple η).Valid := by
  obtain ⟨h1, h2, -, h4, -, h6, -, -⟩ := hv
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro c z
    exact mul_nonneg (regP_nonneg _ _) (regP_nonneg _ _)
  · intro c
    change ∑ z : ZMod p × ZMod p, regP (v.S c) (v.ρ c / 2) (z.1 - v.n c) *
      regP (v.S c) (eps4 η * v.ρ c) z.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [sum_regP _ (by unfold eps4; have := (h4 c).1; positivity), ← Finset.sum_mul, mul_one,
      sum_sub_right (regP (v.S c) (v.ρ c / 2)) (v.n c), sum_regP _ (by linarith [(h4 c).1])]
  · intro c x
    exact h6 c _

variable {v : SLA p} {δ η : ℝ} {f : ZMod p → ℝ}

end SLA

end

end GT
end File_GT_BadEdA

section File_GT_Approx
/-!
# Proposition 3.3 from Theorems 6.6 and 6.7 (Green–Tao §6)

The graph of structured local approximants: the initial approximant (Definition 6.2), the
bounds along short paths (Lemma 6.4), thickness (Corollary 6.5), and the deduction of
`MainAbstract`.
-/

open Finset KM

namespace GT

noncomputable section

namespace SLA

variable {p : ℕ} [NeZero p]

/-- The initial approximant `v₀` (Definition 6.2). -/
def init : SLA p where
  C := ZMod p
  fC := inferInstance
  prob := fun _ => 1 / p
  n := fun c => c
  S := fun _ => {1}
  ρ := fun _ => 1
  G := fun _ => DTorus.point
  F := fun _ _ => 0
  Ξ := fun _ _ => 0

lemma init_valid (hp1 : (1 : ZMod p) ≠ 0) : (init : SLA p).Valid := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  refine ⟨fun _ => by simp only [init]; positivity, ?_, fun _ => ⟨1, by simp [init], hp1⟩,
    fun _ => by simp [init], fun _ => DTorus.point_isLip _, fun _ _ => by simp [init], ?_,
    fun _ => DTorus.point_good⟩
  · show ∑ _c : ZMod p, (1 / (p : ℝ)) = 1
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    field_simp
  · intro c n h₁ h₂ h₃ _ _ _ _ _ _ _ _
    exact funext fun i => Fin.elim0 i

lemma init_d2 : (init : SLA p).d2 = 0 := by
  simp [d2, init, DTorus.point]

lemma init_d1 : (init : SLA p).d1 = 1 := by
  simp only [d1, init, Finset.card_singleton]
  exact Finset.sup_const Finset.univ_nonempty 1

lemma init_rmin : (init : SLA p).rmin = 1 := by
  simp [rmin, init]

lemma init_volm : (init : SLA p).volm = 1 := by
  simp [volm, init, DTorus.point_vol]

lemma init_waste (η : ℝ) (f : ZMod p → ℝ) : (init : SLA p).waste η f = 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hr : 0 ≤ eps4 η * 1 := by unfold eps4; positivity
  unfold waste Triple.ex
  rw [abs_eq_zero, sub_eq_zero]
  simp only [triple, init]
  have inner : ∀ c : ZMod p, ∑ z : ZMod p × ZMod p,
      regP ({1} : Finset (ZMod p)) (1 / 2) (z.1 - c) *
        regP ({1} : Finset (ZMod p)) (eps4 η * 1) z.2 * f z.1 =
      ∑ x, regP ({1} : Finset (ZMod p)) (1 / 2) (x - c) * f x := by
    intro c
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ∑ y : ZMod p, regP ({1} : Finset (ZMod p)) (1 / 2) (x - c) *
        regP ({1} : Finset (ZMod p)) (eps4 η * 1) y * f x =
        regP ({1} : Finset (ZMod p)) (1 / 2) (x - c) * f x *
          ∑ y, regP ({1} : Finset (ZMod p)) (eps4 η * 1) y := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    rw [this, sum_regP _ hr, mul_one]
  simp_rw [inner, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ∑ c : ZMod p, 1 / (p : ℝ) * (regP ({1} : Finset (ZMod p)) (1 / 2) (x - c) * f x) =
      f x / p * ∑ c, regP ({1} : Finset (ZMod p)) (1 / 2) (x - c) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  refine this.trans ?_
  rw [sum_sub_left (regP ({1} : Finset (ZMod p)) (1 / 2)) x, sum_regP _ (by norm_num),
    mul_one]

lemma d2p_le_d2 (v : SLA p) (η : ℝ) : v.d2p η ≤ v.d2 := by
  classical
  unfold d2p d2
  convert Finset.sup_mono (Finset.filter_subset (fun c => v.Poor η c) Finset.univ)

/-- The edge relation used for the graph of Proposition 3.3. -/
def E (η : ℝ) (f : ZMod p → ℝ) (v v' : SLA p) : Prop := v'.Valid ∧ v.Edge η f v'

/-- Statistics along paths from the initial approximant. -/
lemma reach_stats {η : ℝ} {f : ZMod p → ℝ} (hp1 : (1 : ZMod p) ≠ 0) {k : ℕ} {v : SLA p}
    (hr : Reach (E η f) init k v) :
    v.Valid ∧ (v.d1 : ℝ) ≤ 1 + k * (1 / η) ^ C2 ∧ (v.d2 : ℝ) ≤ k ∧
      Real.exp (-(k * (1 / η) ^ C5)) ≤ v.rmin ∧ v.volm ≤ Real.exp (k * (1 / η) ^ C3) ∧
      v.waste η f ≤ k * η ^ C3 := by
  induction hr with
  | zero =>
    refine ⟨init_valid hp1, ?_, ?_, ?_, ?_, ?_⟩
    · simp [init_d1]
    · simp [init_d2]
    · simp [init_rmin]
    · simp [init_volm]
    · simp [init_waste]
  | @step j w w' hr' hE ih =>
    obtain ⟨-, h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨hv', e1, e2, e3, e4, e5⟩ := hE
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    refine ⟨hv', ?_, ?_, ?_, ?_, ?_⟩
    · push_cast; linarith
    · have : (w'.d2 : ℝ) ≤ w.d2 + 1 := by exact_mod_cast e2
      push_cast; linarith
    · refine le_trans ?_ e3
      rw [show -(((j + 1 : ℕ) : ℝ) * (1 / η) ^ C5) = -(1 / η) ^ C5 + -(j * (1 / η) ^ C5) by
        push_cast; ring, Real.exp_add]
      exact mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    · refine e4.trans ?_
      rw [show (((j + 1 : ℕ) : ℝ) * (1 / η) ^ C3) = (1 / η) ^ C3 + j * (1 / η) ^ C3 by
        push_cast; ring, Real.exp_add]
      exact mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    · have := (abs_le.mp e5).1
      push_cast; linarith

end SLA

lemma pow_gap {u : ℝ} (hu : 10 ≤ u) {a b : ℕ} (hab : a + 2 ≤ b) : 100 * u ^ a ≤ u ^ b := by
  have h1 : 100 ≤ u ^ 2 := by nlinarith
  calc 100 * u ^ a ≤ u ^ 2 * u ^ a := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = u ^ (a + 2) := by ring
    _ ≤ u ^ b := pow_le_pow_right₀ (by linarith) hab

lemma consts_facts : 2 ≤ C2 ∧ 2 * C2 + 3 ≤ C3 ∧ 2 * C2 + C3 + 2 ≤ 2 * C3 ∧
    2 * C2 + C5 + 2 ≤ 2 * C5 ∧ C4 ≤ 2 * C5 ∧ 3 * C2 + 2 * C5 + 3 ≤ 3 * C5 := by
  have h2 : C2 = 4294967296 := by unfold C2; norm_num
  have h3 : 4 * C2 ≤ C3 := by
    unfold C2 C3
    calc 4 * 2 ^ 32 = 2 ^ 34 := by norm_num
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h35 : C3 ≤ C5 := by unfold C3 C5; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h45 : C4 ≤ C5 := by unfold C4 C5; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

namespace SLA

variable {p : ℕ} [NeZero p]

/-- **Lemma 6.4**: the bounds hold near the initial approximant. -/
lemma bounds_of_reach {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {f : ZMod p → ℝ}
    (hp1 : (1 : ZMod p) ≠ 0) {k : ℕ} {v : SLA p} (hr : Reach (E η f) init k v)
    (hk : (k : ℝ) ≤ 64 * (1 / η) ^ (2 * C2)) :
    v.Valid ∧ v.Bounds η ∧ v.waste η f ≤ η := by
  obtain ⟨hv, h1, h2, h3, h4, h5⟩ := reach_stats hp1 hr
  obtain ⟨c1, c2, c3, c4, -, -⟩ := consts_facts
  set u := 1 / η with hu
  have hu10 : 10 ≤ u := by rw [hu, le_div_iff₀ hη0]; linarith
  have hu1 : 1 ≤ u := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨hv, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have : (k : ℝ) * u ^ C2 ≤ 64 * u ^ (3 * C2) := by
      calc (k : ℝ) * u ^ C2 ≤ 64 * u ^ (2 * C2) * u ^ C2 :=
            mul_le_mul_of_nonneg_right hk (by positivity)
        _ = 64 * u ^ (3 * C2) := by ring
    have : (1 : ℝ) ≤ u ^ (3 * C2) := one_le_pow₀ hu1
    linarith
  · linarith
  · rw [← hu]
    refine le_trans (Real.exp_le_exp.mpr ?_) h3
    have : (k : ℝ) * u ^ C5 ≤ 64 * u ^ (2 * C2 + C5) := by
      calc (k : ℝ) * u ^ C5 ≤ 64 * u ^ (2 * C2) * u ^ C5 :=
            mul_le_mul_of_nonneg_right hk (by positivity)
        _ = 64 * u ^ (2 * C2 + C5) := by ring
    have := pow_gap hu10 c4
    have : 0 ≤ u ^ (2 * C2 + C5) := by positivity
    linarith
  · rw [← hu]
    refine h4.trans (Real.exp_le_exp.mpr ?_)
    have : (k : ℝ) * u ^ C3 ≤ 64 * u ^ (2 * C2 + C3) := by
      calc (k : ℝ) * u ^ C3 ≤ 64 * u ^ (2 * C2) * u ^ C3 :=
            mul_le_mul_of_nonneg_right hk (by positivity)
        _ = 64 * u ^ (2 * C2 + C3) := by ring
    have := pow_gap hu10 c3
    have : 0 ≤ u ^ (2 * C2 + C3) := by positivity
    linarith
  · refine h5.trans ?_
    have hη' : η = 1 / u := by rw [hu, one_div_one_div]
    have e : η ^ C3 = 1 / u ^ C3 := by rw [hη', one_div_pow]
    rw [e, hη', mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have := pow_gap hu10 (a := 2 * C2 + 1) (b := C3) (by omega)
    calc (k : ℝ) * u ≤ 64 * u ^ (2 * C2) * u := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = 64 * u ^ (2 * C2 + 1) := by ring
      _ ≤ u ^ C3 := by linarith [pow_pos (by linarith : (0 : ℝ) < u) (2 * C2 + 1)]

/-- **Corollary 6.5** (thickness). -/
lemma pzero_le {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {v : SLA p} (hv : v.Valid)
    (hb : v.Bounds η) : (v.triple η).pzero ≤ Real.exp ((1 / η) ^ (3 * C5)) / p := by
  classical
  obtain ⟨hpr, hsum, -, hρ, -, -, -, -⟩ := hv
  obtain ⟨hd1, -, hrm, -⟩ := hb
  obtain ⟨-, -, -, -, c5, c6⟩ := consts_facts
  set u := 1 / η with hu
  have hu10 : 10 ≤ u := by rw [hu, le_div_iff₀ hη0]; linarith
  have hu1 : 1 ≤ u := by linarith
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have key : ∀ c, regP (v.S c) (eps4 η * v.ρ c) 0 ≤ Real.exp (u ^ (3 * C5)) / p := by
    intro c
    have hρc := hρ c
    have he0 : 0 < eps4 η := Real.exp_pos _
    have he1 : eps4 η ≤ 1 := by
      unfold eps4; rw [Real.exp_le_one_iff]; have : 0 ≤ (1 / η) ^ C4 := by positivity
      linarith
    have hx0 : 0 < eps4 η * v.ρ c := mul_pos he0 hρc.1
    have hx1 : eps4 η * v.ρ c ≤ 1 := mul_le_one₀ he1 hρc.1.le hρc.2
    refine (regP_le _ hx0 hx1 0).trans ?_
    set x := eps4 η * v.ρ c / 4 with hxdef
    have hx : 0 < x := by positivity
    have hxle : x ≤ 1 := by rw [hxdef]; linarith
    have hs : ((v.S c).card : ℝ) ≤ 65 * u ^ (3 * C2) := le_trans
      (by exact_mod_cast Finset.le_sup (f := fun c => (v.S c).card) (Finset.mem_univ c)) hd1
    have hlogρ : -u ^ (2 * C5) ≤ Real.log (v.ρ c) := by
      rw [← Real.log_exp (-u ^ (2 * C5))]
      exact Real.log_le_log (Real.exp_pos _)
        (hrm.trans (ciInf_le (Set.finite_range _).bddBelow c))
    have hlogx : Real.log x = -u ^ C4 + Real.log (v.ρ c) - Real.log 4 := by
      rw [hxdef, Real.log_div hx0.ne' (by norm_num), Real.log_mul he0.ne' hρc.1.ne']
      unfold eps4; rw [Real.log_exp]
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have hlog4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hC4 : u ^ C4 ≤ u ^ (2 * C5) := pow_le_pow_right₀ hu1 c5
    have hbig : 1 ≤ u ^ (2 * C5) := one_le_pow₀ hu1
    have hneg : -Real.log x ≤ 5 * u ^ (2 * C5) := by linarith
    have hneg0 : 0 ≤ -Real.log x := by linarith [Real.log_nonpos hx.le hxle]
    have hu3 : 325 ≤ u ^ 3 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu10 3)
    have hprod : ((v.S c).card : ℝ) * (-Real.log x) ≤ u ^ (3 * C5) := by
      calc ((v.S c).card : ℝ) * (-Real.log x) ≤ 65 * u ^ (3 * C2) * (5 * u ^ (2 * C5)) :=
            mul_le_mul hs hneg hneg0 (by positivity)
        _ = 325 * u ^ (3 * C2 + 2 * C5) := by ring
        _ ≤ u ^ 3 * u ^ (3 * C2 + 2 * C5) :=
            mul_le_mul_of_nonneg_right hu3 (by positivity)
        _ = u ^ (3 * C2 + 2 * C5 + 3) := by ring
        _ ≤ u ^ (3 * C5) := pow_le_pow_right₀ hu1 c6
    have hxs : x ^ (v.S c).card = Real.exp ((v.S c).card * Real.log x) := by
      rw [← Real.exp_log hx, ← Real.exp_nat_mul, Real.log_exp]
    rw [hxs, one_div, mul_inv, mul_comm, ← Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hp.le
  have hpz : (v.triple η).pzero = ∑ c, v.prob c * regP (v.S c) (eps4 η * v.ρ c) 0 := by
    unfold Triple.pzero triple
    refine Finset.sum_congr rfl fun c _ => ?_
    (try dsimp only)
    rw [← Finset.sum_mul, sum_sub_right (regP (v.S c) (v.ρ c / 2)) (v.n c),
      sum_regP _ (by linarith [(hρ c).1]), one_mul]
  calc (v.triple η).pzero = ∑ c, v.prob c * regP (v.S c) (eps4 η * v.ρ c) 0 := hpz
    _ ≤ ∑ c, v.prob c * (Real.exp (u ^ (3 * C5)) / p) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (key c) (hpr c)
    _ = Real.exp (u ^ (3 * C5)) / p := by rw [← Finset.sum_mul, hsum, one_mul]

end SLA

/-- **Proposition 3.3** of Green–Tao. -/
theorem mainAbstract : ∃ C₂ C₅ : ℕ, 2 ≤ C₂ ∧ MainAbstract C₂ C₅ := by
  refine ⟨C2, 3 * C5, consts_facts.1, ?_⟩
  intro p _ hp η hη0 hη1 hpη f hf
  have hp1 : (1 : ZMod p) ≠ 0 := by
    haveI := Fact.mk hp
    exact one_ne_zero
  have hu1 : 1 ≤ 1 / η := by rw [le_div_iff₀ hη0]; linarith
  have hpη' : Real.exp ((1 / η) ^ (3 * C5)) ≤ p :=
    le_trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hu1 (by omega))) hpη
  refine ⟨SLA p, SLA.E η f, fun v => v.triple η, fun v => v.d2, fun v => v.d2p η, SLA.init,
    SLA.init_d2, fun v => SLA.d2p_le_d2 v η, ?_⟩
  intro k v hr hk
  obtain ⟨hv, hb, hw⟩ := SLA.bounds_of_reach hη0 hη1 hp1 hr hk
  refine ⟨SLA.triple_valid hv η, SLA.pzero_le hη0 hη1 hv hb, hw, ?_, ?_⟩
  · intro hbad
    obtain ⟨v', hv', hedge, hen⟩ := bad_ed_thm hp hη0 hη1 hpη' hf hv hb hbad
    exact ⟨v', ⟨hv', hedge⟩, hen, hedge.2.1⟩
  · intro hlow
    obtain ⟨v', hv', hedge, hd2, hdp, hen⟩ := bad_dim_thm hp hη0 hη1 hpη' hf hv hb hlow
    exact ⟨v', ⟨hv', hedge⟩, hen, hd2, hdp⟩

end

end GT
end File_GT_Approx

section File_KM_Final
/-!
# The Kelley–Meka bound `r_3(N) ≤ N exp(-(log N)^{1/12})`
-/

open Finset

namespace KM

noncomputable section

/-- A progression with positive difference and `k > 1` terms is a progression in the sense of
`Erdos142.IsAPOfLength`. -/
theorem not_isAPOfLengthFree_of_ap' (k : ℕ) (hk : 1 < k) (S : Finset ℕ) (a d : ℕ) (hd : 0 < d)
    (h : ∀ i < k, a + i * d ∈ S) : ¬ Erdos142.IsAPOfLengthFree (S : Set ℕ) k := by
  intro hfree
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro x y hxy
    simp only at hxy
    have := Nat.eq_of_mul_eq_mul_right hd (by omega : x * d = y * d)
    exact this
  refine absurd (hfree _ ?_ ⟨a, d, ?_, rfl⟩) ?_
  · rintro x ⟨n, hn, rfl⟩
    rw [smul_eq_mul]
    exact h n (by exact_mod_cast hn)
  · rw [ENat.card_coe_set_eq]
    have : {x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} =
        (((Finset.range k).image (fun n : ℕ => a + n * d) : Finset ℕ) : Set ℕ) := by
      ext x
      simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
        Set.mem_Iio, smul_eq_mul, Nat.cast_lt, exists_prop]
    rw [this, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
      Finset.card_range]
  · intro hle
    have : k ≤ 1 := by exact_mod_cast hle
    omega

lemma natCast_eq_of_lt {N a b : ℕ} (ha : a < N) (hb : b < N) (h : (a : ZMod N) = b) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff' a b N, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

end

end KM

namespace Erdos142

end Erdos142
end File_KM_Final

section File_GT_Final
/-!
# Green–Tao: `r_4(N) ≤ N (log N)^{-c}`, deduced from the Khintchine-type recurrence theorem
-/

open Finset

namespace GT

noncomputable section

/-- The indicator function of (the image of) `A` in `ZMod p`. -/
def indZ (p : ℕ) (A : Finset ℕ) (x : ZMod p) : ℝ :=
  if x ∈ A.image (Nat.cast : ℕ → ZMod p) then 1 else 0

lemma indZ_nonneg (p : ℕ) (A : Finset ℕ) (x : ZMod p) : 0 ≤ indZ p A x := by
  unfold indZ; split_ifs <;> norm_num

lemma indZ_le_one (p : ℕ) (A : Finset ℕ) (x : ZMod p) : indZ p A x ≤ 1 := by
  unfold indZ; split_ifs <;> norm_num

lemma card_image_cast {p N : ℕ} (hp : N < p) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) :
    (A.image (Nat.cast : ℕ → ZMod p)).card = A.card := by
  apply card_image_of_injOn
  intro a ha b hb hab
  have ha1 := mem_Icc.mp (hA ha)
  have hb1 := mem_Icc.mp (hA hb)
  exact KM.natCast_eq_of_lt (by omega) (by omega) hab

lemma sum_indZ {p N : ℕ} [NeZero p] (hp : N < p) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) :
    ∑ x, indZ p A x / p = A.card / p := by
  rw [← Finset.sum_div]
  congr 1
  unfold indZ
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
    card_image_cast hp hA]

/-- A set of naturals in `[1, N]` without 4-term progressions has no non-trivial 4-term
progressions modulo `p > 2N`. -/
lemma indZ_prod_eq_zero {p N : ℕ} [NeZero p] (hp : 2 * N < p) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ A)
    (a r : ZMod p) (hr : r ≠ 0) :
    indZ p A a * indZ p A (a + r) * indZ p A (a + 2 * r) * indZ p A (a + 3 * r) = 0 := by
  by_contra hne
  have h1 : a ∈ A.image (Nat.cast : ℕ → ZMod p) := by
    by_contra h; apply hne; simp [indZ, h]
  have h2 : a + r ∈ A.image (Nat.cast : ℕ → ZMod p) := by
    by_contra h; apply hne; simp [indZ, h]
  have h3 : a + 2 * r ∈ A.image (Nat.cast : ℕ → ZMod p) := by
    by_contra h; apply hne; simp [indZ, h]
  have h4 : a + 3 * r ∈ A.image (Nat.cast : ℕ → ZMod p) := by
    by_contra h; apply hne; simp [indZ, h]
  rw [mem_image] at h1 h2 h3 h4
  obtain ⟨x, hx, ex⟩ := h1
  obtain ⟨y, hy, ey⟩ := h2
  obtain ⟨z, hz, ez⟩ := h3
  obtain ⟨u, hu, eu⟩ := h4
  have hx1 := mem_Icc.mp (hA hx)
  have hy1 := mem_Icc.mp (hA hy)
  have hz1 := mem_Icc.mp (hA hz)
  have hu1 := mem_Icc.mp (hA hu)
  have e1 : x + z = y + y := by
    apply KM.natCast_eq_of_lt (N := p) (by omega) (by omega)
    push_cast; rw [ex, ey, ez]; ring
  have e2 : y + u = z + z := by
    apply KM.natCast_eq_of_lt (N := p) (by omega) (by omega)
    push_cast; rw [ey, ez, eu]; ring
  have hxy : x ≠ y := by
    intro h
    apply hr
    have : ((y : ℕ) : ZMod p) - x = r := by rw [ex, ey]; ring
    rw [← this, h, sub_self]
  apply hno
  rcases lt_or_gt_of_ne hxy with h | h
  · refine ⟨x, y - x, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hx
    · rw [show x + 1 * (y - x) = y by omega]; exact hy
    · rw [show x + 2 * (y - x) = z by omega]; exact hz
    · rw [show x + 3 * (y - x) = u by omega]; exact hu
  · refine ⟨u, x - y, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hu
    · rw [show u + 1 * (x - y) = z by omega]; exact hz
    · rw [show u + 2 * (x - y) = y by omega]; exact hy
    · rw [show u + 3 * (x - y) = x by omega]; exact hx

lemma lam4_le_of_zero {p : ℕ} [NeZero p] (w : ZMod p × ZMod p → ℝ) (hw : ∀ z, 0 ≤ w z)
    (f : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (h0 : ∀ a r : ZMod p, r ≠ 0 → f a * f (a + r) * f (a + 2 * r) * f (a + 3 * r) = 0) :
    lam4 w f ≤ ∑ a, w (a, 0) := by
  unfold lam4
  have key : ∀ z : ZMod p × ZMod p,
      w z * (f z.1 * f (z.1 + z.2) * f (z.1 + 2 * z.2) * f (z.1 + 3 * z.2)) ≤
        if z.2 = 0 then w z else 0 := by
    intro z
    split_ifs with hz
    · have hb : f z.1 * f (z.1 + z.2) * f (z.1 + 2 * z.2) * f (z.1 + 3 * z.2) ≤ 1 := by
        have a1 := hf z.1; have a2 := hf (z.1 + z.2)
        have a3 := hf (z.1 + 2 * z.2); have a4 := hf (z.1 + 3 * z.2)
        have b1 : f z.1 * f (z.1 + z.2) ≤ 1 := mul_le_one₀ a1.2 a2.1 a2.2
        have b2 : f z.1 * f (z.1 + z.2) * f (z.1 + 2 * z.2) ≤ 1 :=
          mul_le_one₀ b1 a3.1 a3.2
        exact mul_le_one₀ b2 a4.1 a4.2
      calc _ ≤ w z * 1 := mul_le_mul_of_nonneg_left hb (hw z)
        _ = w z := mul_one _
    · rw [h0 z.1 z.2 hz, mul_zero]
  refine (Finset.sum_le_sum fun z _ => key z).trans (le_of_eq ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod p) (fun b => w (a, b))]
  simp

/-- The core consequence of the recurrence theorem: a set of density `α` in `ZMod p` whose
4-term progressions are all trivial satisfies `log p ≤ K α^{-4C}`. -/
lemma core_bound {C : ℕ} (hC : 0 < C) (hkh : ∀ (p : ℕ) [NeZero p], p.Prime → ∀ η : ℝ, 0 < η →
    η ≤ 1 / 10 → ∀ f : ZMod p → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      ∃ w : ZMod p × ZMod p → ℝ, (∀ z, 0 ≤ w z) ∧ ∑ z, w z = 1 ∧
        (∑ x, f x / p) ^ 4 - C * η ≤ lam4 w f ∧
        ∑ a, w (a, 0) ≤ Real.exp ((1 / η) ^ C) / p)
    {p : ℕ} [NeZero p] (hp : p.Prime) (f : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (h0 : ∀ a r : ZMod p, r ≠ 0 → f a * f (a + r) * f (a + 2 * r) * f (a + 3 * r) = 0)
    {α : ℝ} (hα : α = ∑ x, f x / p) (hα0 : 0 < α) (hα1 : α ≤ 1 / 2) :
    Real.log p ≤ (5 + (2 * C : ℝ) ^ C) * (1 / α) ^ (4 * C) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set η : ℝ := α ^ 4 / (2 * C) with hη
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 10 := by
    rw [hη, div_le_iff₀ (by positivity)]
    have : α ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ hα0.le hα1 4
    have h1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith
  obtain ⟨w, hw, -, hlam, hzero⟩ := hkh p hp η hη0 hη1 f hf
  have hle := lam4_le_of_zero w hw f hf h0
  rw [← hα] at hlam
  have hCη : (C : ℝ) * η = α ^ 4 / 2 := by rw [hη]; field_simp
  have hmain : α ^ 4 / 2 ≤ Real.exp ((1 / η) ^ C) / p := by linarith
  have hinv : 1 / η = 2 * C * (1 / α) ^ 4 := by rw [hη]; field_simp
  set u : ℝ := 1 / α with hu
  have hu1 : 1 ≤ u := by
    rw [hu, le_div_iff₀ hα0]; linarith
  have hu0 : 0 < u := by linarith
  -- p ≤ 2 u^4 exp((2C)^C u^{4C})
  have hpbound : (p : ℝ) ≤ 2 * u ^ 4 * Real.exp ((2 * C) ^ C * u ^ (4 * C)) := by
    have e1 : (1 / η) ^ C = (2 * C) ^ C * u ^ (4 * C) := by
      rw [hinv, mul_pow, pow_mul]
    rw [e1] at hmain
    have hα4 : α ^ 4 = 1 / u ^ 4 := by rw [hu]; field_simp
    rw [hα4, le_div_iff₀ hp0] at hmain
    have hu4 : 0 < u ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ 2 * u ^ 4)
    have e2 : 2 * u ^ 4 * (1 / u ^ 4 / 2 * p) = p := by field_simp
    linarith
  have hlogp : Real.log p ≤ Real.log 2 + 4 * Real.log u + (2 * C) ^ C * u ^ (4 * C) := by
    have := Real.log_le_log hp0 hpbound
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_exp] at this
    push_cast at this
    linarith
  have hlogu : Real.log u ≤ u := (Real.log_le_sub_one_of_pos hu0).trans (by linarith)
  have hu4C : u ≤ u ^ (4 * C) := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ (4 * C) := pow_le_pow_right₀ hu1 (by omega)
  have h1 : (1 : ℝ) ≤ u ^ (4 * C) := one_le_pow₀ hu1
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have : Real.log u ≤ u ^ (4 * C) := hlogu.trans hu4C
  linarith

lemma rpow_pow_eq {x : ℝ} (hx : 0 ≤ x) {C : ℕ} (hC : 0 < C) :
    (x ^ ((1 : ℝ) / (8 * C))) ^ (4 * C) = x ^ ((1 : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  have : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  push_cast
  field_simp
  ring

/-- **Green–Tao (2017)** from the Khintchine-type recurrence theorem. -/
theorem green_tao_four_of_khint (hK : KhintProp) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (Erdos142.r 4 N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ c := by
  obtain ⟨C, hC, hkh⟩ := hK
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  set K : ℝ := (5 + (2 * C : ℝ) ^ C) * 4 ^ (4 * C) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨1 / (8 * C), by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨⌈Real.exp (K ^ 2)⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hNexp : Real.exp (K ^ 2) < N := by
    have := Nat.le_ceil (Real.exp (K ^ 2))
    have : (⌈Real.exp (K ^ 2)⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  have hlogN : K ^ 2 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]; exact hNexp
  have hlog0 : 0 < Real.log N := lt_of_le_of_lt (by positivity) hlogN
  -- reduce to a statement about a single progression-free set
  have hne : {x | ∃ (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : Erdos142.IsAPOfLengthFree (S : Set ℕ) 4), S.card = x}.Nonempty :=
    ⟨0, ∅, by simp, by simpa using Erdos142.isAPOfLengthFree_empty (α := ℕ) 4, rfl⟩
  have hbdd : BddAbove {x | ∃ (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : Erdos142.IsAPOfLengthFree (S : Set ℕ) 4), S.card = x} := by
    refine ⟨N, ?_⟩
    rintro m ⟨T, hT, -, rfl⟩
    simpa using (Finset.card_le_card hT).trans_eq (by simp)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hne hbdd
  have hr : Erdos142.r 4 N = S.card := by rw [hcard]; rfl
  rw [hr]
  have hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S := by
    rintro ⟨a, d, hd, hap⟩
    exact KM.not_isAPOfLengthFree_of_ap' 4 (by norm_num) S a d hd hap hfree
  have hRHS0 : 0 ≤ (N : ℝ) / Real.log N ^ (1 / (8 * (C : ℝ))) := by positivity
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.card_empty, Nat.cast_zero]; exact hRHS0
  by_contra hbig
  push_neg at hbig
  -- choose a prime `2N < p ≤ 4N`
  obtain ⟨p, hpp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hSN : S.card ≤ N := by simpa using (Finset.card_le_card hS)
  have hScard0 : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1r : (2 * N : ℝ) < p := by exact_mod_cast hp1
  have hp2r : (p : ℝ) ≤ 4 * N := by exact_mod_cast (by omega : p ≤ 4 * N)
  have hcore := core_bound hC hkh hpp (indZ p S) (fun x => ⟨indZ_nonneg p S x, indZ_le_one p S x⟩)
    (fun a r hr => indZ_prod_eq_zero hp1 hS hno a r hr) (α := S.card / p)
    (sum_indZ (by omega) hS).symm (by positivity)
    (by
      rw [div_le_iff₀ hp0]
      have : (S.card : ℝ) ≤ N := by exact_mod_cast hSN
      linarith)
  -- log N ≤ K (N / |S|)^{4C}
  have hlogNp : Real.log N ≤ Real.log p := Real.log_le_log (by linarith) (by linarith)
  have hinv : 1 / ((S.card : ℝ) / p) ≤ 4 * (N / S.card) := by
    rw [one_div_div, div_le_iff₀ hScard0]
    field_simp
    linarith
  have hpow : (1 / ((S.card : ℝ) / p)) ^ (4 * C) ≤ 4 ^ (4 * C) * (N / S.card) ^ (4 * C) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hinv _
  have hlogK : Real.log N ≤ K * (N / S.card) ^ (4 * C) := by
    calc Real.log N ≤ (5 + (2 * C : ℝ) ^ C) * (1 / ((S.card : ℝ) / p)) ^ (4 * C) :=
          hlogNp.trans hcore
      _ ≤ (5 + (2 * C : ℝ) ^ C) * (4 ^ (4 * C) * (N / S.card) ^ (4 * C)) := by gcongr
      _ = K * (N / S.card) ^ (4 * C) := by rw [hK]; ring
  -- N / |S| < (log N)^c
  set L : ℝ := Real.log N ^ (1 / (8 * (C : ℝ))) with hL
  have hL0 : 0 < L := Real.rpow_pos_of_pos hlog0 _
  have hratio : (N : ℝ) / S.card < L := by
    rw [div_lt_iff₀ hScard0]
    rw [div_lt_iff₀ hL0] at hbig
    linarith
  have hpowL : ((N : ℝ) / S.card) ^ (4 * C) < L ^ (4 * C) :=
    pow_lt_pow_left₀ hratio (by positivity) (by omega)
  rw [hL, rpow_pow_eq hlog0.le hC] at hpowL
  set s : ℝ := Real.log N ^ ((1 : ℝ) / 2) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hlog0 _
  have hss : s * s = Real.log N := by
    rw [hs, ← Real.rpow_add hlog0]; norm_num
  have h1 : s * s < K * s := by
    rw [hss]
    calc Real.log N ≤ K * (N / S.card) ^ (4 * C) := hlogK
      _ < K * s := by
        apply mul_lt_mul_of_pos_left _ hK0
        simpa [hs] using hpowL
  have h2 : s < K := lt_of_mul_lt_mul_right (by linarith) hs0.le
  have h3 : s * s < K ^ 2 := by nlinarith
  rw [hss] at h3
  linarith

end

end GT

namespace GT

/-- **Theorem 3.1** of Green–Tao. -/
theorem khint : KhintProp := by
  obtain ⟨C₂, C₅, hC₂, h⟩ := mainAbstract
  exact khint_of_mainAbstract hC₂ h

end GT

namespace Erdos142

/-- **Green–Tao (2017).** There is `c > 0` with `r_4(N) ≤ N (log N)^{-c}` for all large `N`. -/
theorem green_tao_four :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r 4 N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ c :=
  GT.green_tao_four_of_khint GT.khint

end Erdos142
end File_GT_Final

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (Erdos142.r 4 N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ c :=
  Erdos142.green_tao_four

