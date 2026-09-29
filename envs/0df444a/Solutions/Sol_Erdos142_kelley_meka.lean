-- Prove2me | solution 1 for Erdos142.kelley_meka
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-26T18:33:03.833619+00:00
-- url     : https://prove2.me/submissions/5d814d7b-4bf2-4154-a808-dd21a979c32e

import Mathlib
import Definitions.Def_Erdos142Basic

section KMFile_Bohr



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

/-- The distance from `z / N` to the nearest integer. -/
def cn (z : ZMod N) : ℝ := ‖ZMod.toAddCircle z‖

lemma cn_nonneg (z : ZMod N) : 0 ≤ cn z := norm_nonneg _

@[simp] lemma cn_neg (z : ZMod N) : cn (-z) = cn z := by simp [cn]

@[simp] lemma cn_zero : cn (0 : ZMod N) = 0 := by simp [cn]

lemma cn_add_le (a b : ZMod N) : cn (a + b) ≤ cn a + cn b := by
  simp only [cn, map_add]; exact norm_add_le _ _

lemma cn_sub_le (a b : ZMod N) : cn (a - b) ≤ cn a + cn b := by
  rw [sub_eq_add_neg]; exact (cn_add_le _ _).trans (by rw [cn_neg])

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

/-- The Bohr set with frequency set `Γ` and radius `ρ`. -/
def bohr (Γ : Finset (ZMod N)) (ρ : ℝ) : Finset (ZMod N) :=
  univ.filter fun x => ∀ γ ∈ Γ, cn (γ * x) ≤ ρ

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

@[simp] lemma bohr_empty : bohr (∅ : Finset (ZMod N)) ρ = univ := by
  ext; simp

lemma bohr_eq_univ (h : 1 / 2 ≤ ρ) : bohr Γ ρ = univ := by
  ext x; simp only [mem_bohr, mem_univ, iff_true]
  exact fun γ _ => (cn_le_half _).trans h

lemma bohr_nonempty (hρ : 0 ≤ ρ) : (bohr Γ ρ).Nonempty := ⟨0, zero_mem_bohr hρ⟩

lemma bohr_card_pos (hρ : 0 ≤ ρ) : 0 < (bohr Γ ρ).card := (bohr_nonempty hρ).card_pos

lemma bohr_union : bohr (Γ ∪ Γ') ρ = bohr Γ ρ ∩ bohr Γ' ρ := by
  ext x; simp only [mem_bohr, mem_union, mem_inter]
  constructor
  · intro h; exact ⟨fun γ hγ => h γ (Or.inl hγ), fun γ hγ => h γ (Or.inr hγ)⟩
  · rintro ⟨h1, h2⟩ γ (hγ | hγ)
    exacts [h1 γ hγ, h2 γ hγ]

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

lemma card_bohr_mono (Γ : Finset (ZMod N)) (h : ρ ≤ ρ') :
    ((bohr Γ ρ).card : ℝ) ≤ (bohr Γ ρ').card := by
  exact_mod_cast card_le_card (bohr_mono h)

/-! ### Regularity -/

/-- A Bohr set `bohr Γ ρ` is `(κ, ε)`-regular if its `(1+κ)` dilate is at most `1+ε` times its
`(1-κ)` dilate. -/
def IsReg (Γ : Finset (ZMod N)) (ρ κ ε : ℝ) : Prop :=
  ((bohr Γ (ρ * (1 + κ))).card : ℝ) ≤ (1 + ε) * (bohr Γ (ρ * (1 - κ))).card

lemma IsReg.mono {κ κ' ε : ℝ} (h : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ) (hκ : κ' ≤ κ)
    (hε : 0 ≤ ε) : IsReg Γ ρ κ' ε := by
  unfold IsReg at *
  calc ((bohr Γ (ρ * (1 + κ'))).card : ℝ) ≤ (bohr Γ (ρ * (1 + κ))).card :=
        card_bohr_mono Γ (by nlinarith)
    _ ≤ (1 + ε) * (bohr Γ (ρ * (1 - κ))).card := h
    _ ≤ (1 + ε) * (bohr Γ (ρ * (1 - κ'))).card := by
        gcongr
        exact bohr_mono (by nlinarith)

lemma IsReg.card_upper {κ ε : ℝ} (h : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) :
    ((bohr Γ (ρ * (1 + κ))).card : ℝ) ≤ (1 + ε) * (bohr Γ ρ).card := by
  refine h.trans ?_
  gcongr
  exact bohr_mono (by nlinarith)

lemma IsReg.card_lower {κ ε : ℝ} (h : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) :
    ((bohr Γ ρ).card : ℝ) ≤ (1 + ε) * (bohr Γ (ρ * (1 - κ))).card := by
  refine le_trans ?_ h
  exact card_bohr_mono Γ (by nlinarith)

/-- For `y` in the `κ`-dilate, few elements `x` of a regular Bohr set have `x - y` outside. -/
lemma IsReg.card_sdiff_le {κ ε : ℝ} (h : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hy : y ∈ bohr Γ (κ * ρ)) :
    (((bohr Γ ρ).filter (fun x => x - y ∉ bohr Γ ρ)).card : ℝ) ≤ ε * (bohr Γ ρ).card := by
  have hsub : (bohr Γ ρ).filter (fun x => x - y ∉ bohr Γ ρ) ⊆
      bohr Γ ρ \ bohr Γ (ρ * (1 - κ)) := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_sdiff]
    refine ⟨hx.1, fun hx' => hx.2 ?_⟩
    have := sub_mem_bohr hx' hy
    rwa [show ρ * (1 - κ) + κ * ρ = ρ by ring] at this
  have hsub2 : bohr Γ (ρ * (1 - κ)) ⊆ bohr Γ ρ := bohr_mono (by nlinarith)
  have h1 := card_le_card hsub
  rw [card_sdiff_of_subset hsub2] at h1
  have h2 := h.card_lower hρ hκ
  have hB : (0 : ℝ) ≤ (bohr Γ (ρ * (1 - κ))).card := by positivity
  have h1' : (((bohr Γ ρ).filter (fun x => x - y ∉ bohr Γ ρ)).card : ℝ) ≤
      (bohr Γ ρ).card - (bohr Γ (ρ * (1 - κ))).card := by
    have := Nat.cast_le (α := ℝ) |>.mpr h1
    rwa [Nat.cast_sub (card_le_card hsub2)] at this
  nlinarith

theorem exists_reg (Γ : Finset (ZMod N)) (hρ : 0 < ρ) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ ≤ 1 / 8)
    (hd : 32 * κ * Γ.card ≤ 1) :
    ∃ ρ₁, ρ / 2 ≤ ρ₁ ∧ ρ₁ ≤ ρ ∧ IsReg Γ ρ₁ κ (32 * κ * Γ.card) := by
  by_contra hcon
  push_neg at hcon
  set d := Γ.card with hd_def
  set ε := 32 * κ * d with hε_def
  have hε0 : 0 ≤ ε := by positivity
  set J := ⌊1 / (4 * κ)⌋₊ with hJ_def
  have h4κ : 0 < 4 * κ := by positivity
  have hJκ : (J : ℝ) * (4 * κ) ≤ 1 := by
    have := Nat.floor_le (a := 1 / (4 * κ)) (by positivity)
    rw [← hJ_def] at this
    rwa [le_div_iff₀ h4κ] at this
  have hJlt : 1 / (4 * κ) < J + 1 := by rw [hJ_def]; exact Nat.lt_floor_add_one _
  have hJ8 : 1 / (8 * κ) ≤ J := by
    have : 1 / (8 * κ) ≤ 1 / (4 * κ) - 1 := by
      rw [div_sub_one h4κ.ne', div_le_div_iff₀ (by positivity) h4κ]; nlinarith
    linarith
  have hJ1 : 1 ≤ J := by
    have : (1 : ℝ) ≤ 1 / (8 * κ) := by rw [le_div_iff₀ (by positivity)]; linarith
    exact_mod_cast this.trans hJ8
  let a : ℕ → ℝ := fun j => ρ / 2 + 2 * j * κ * ρ
  let c : ℕ → ℝ := fun j => (bohr Γ (a j)).card
  have step : ∀ j < J, (1 + ε) * c j < c (j + 1) := by
    intro j hj
    have hj' : ((j : ℝ) + 1) ≤ J := by exact_mod_cast hj
    set ρ₁ := a j + κ * ρ with hρ₁
    have hjκ : 0 ≤ 2 * (j : ℝ) * κ * ρ + κ * ρ := by positivity
    have hρ₁1 : ρ / 2 ≤ ρ₁ := by simp only [ρ₁, a]; linarith
    have h1 : (2 * (j : ℝ) + 1) ≤ 2 * J := by linarith
    have h2 : (2 * (j : ℝ) + 1) * (κ * ρ) ≤ 2 * J * (κ * ρ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 2 * (J : ℝ) * (κ * ρ) ≤ ρ / 2 := by nlinarith
    have hρ₁2 : ρ₁ ≤ ρ := by
      simp only [ρ₁, a]
      nlinarith
    have hreg := hcon ρ₁ hρ₁1 hρ₁2
    unfold IsReg at hreg
    push_neg at hreg
    have hκρ : κ * ρ₁ ≤ κ * ρ := mul_le_mul_of_nonneg_left hρ₁2 hκ.le
    have ha1 : a j ≤ ρ₁ * (1 - κ) := by
      have : ρ₁ * (1 - κ) = ρ₁ - κ * ρ₁ := by ring
      rw [this]; simp only [ρ₁] at hκρ ⊢; linarith
    have ha2 : ρ₁ * (1 + κ) ≤ a (j + 1) := by
      have : ρ₁ * (1 + κ) = ρ₁ + κ * ρ₁ := by ring
      rw [this]; simp only [ρ₁, a] at hκρ ⊢; push_cast; linarith
    calc (1 + ε) * c j ≤ (1 + ε) * (bohr Γ (ρ₁ * (1 - κ))).card := by
          gcongr; exact card_bohr_mono Γ ha1
      _ < (bohr Γ (ρ₁ * (1 + κ))).card := hreg
      _ ≤ c (j + 1) := card_bohr_mono Γ ha2
  have chain : ∀ j ≤ J, (1 + ε) ^ j * c 0 ≤ c j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have := step j (by omega)
      calc (1 + ε) ^ (j + 1) * c 0 = (1 + ε) * ((1 + ε) ^ j * c 0) := by ring
        _ ≤ (1 + ε) * c j := by gcongr; exact ih (by omega)
        _ ≤ c (j + 1) := this.le
  have hc0 : 0 < c 0 := by
    simp only [c]; exact_mod_cast bohr_card_pos (by simp only [a]; positivity)
  have strict : (1 + ε) ^ J * c 0 < c J := by
    obtain ⟨J', hJ'⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    rw [hJ']
    have := step J' (by omega)
    calc (1 + ε) ^ (J' + 1) * c 0 = (1 + ε) * ((1 + ε) ^ J' * c 0) := by ring
      _ ≤ (1 + ε) * c J' := by gcongr; exact chain J' (by omega)
      _ < c (J' + 1) := this
  have upper : c J ≤ 8 ^ d * c 0 := by
    have haJ : a J ≤ ρ := by
      have : 2 * (J : ℝ) * κ * ρ ≤ ρ / 2 := by nlinarith
      simp only [a]; linarith
    have h1 : c J ≤ (bohr Γ ρ).card := card_bohr_mono Γ haJ
    have h2 := card_bohr_le Γ (ρ := ρ) (ρ' := ρ / 2) (by positivity) (by linarith)
    have e : 4 * ρ / (ρ / 2) = 8 := by field_simp; norm_num
    rw [e] at h2
    have e2 : a 0 = ρ / 2 := by simp [a]
    simp only [c, e2] at h1 ⊢
    linarith
  have lower : (8 : ℝ) ^ d ≤ (1 + ε) ^ J := by
    have hε1 : ε ≤ 1 := hd
    have hb : (2 : ℝ) ^ ε ≤ 1 + ε := by
      have := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hε0 hε1
      norm_num at this ⊢; linarith
    have h3 : (3 * d : ℝ) ≤ ε * J := by
      have : ε * J ≥ 32 * κ * d * (1 / (8 * κ)) := by
        rw [hε_def]; gcongr
      have e : 32 * κ * (d : ℝ) * (1 / (8 * κ)) = 4 * d := by field_simp; ring
      rw [e] at this
      have : (0 : ℝ) ≤ d := by positivity
      linarith
    calc (8 : ℝ) ^ d = (2 : ℝ) ^ ((3 * d : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; rw [pow_mul]; norm_num
      _ ≤ (2 : ℝ) ^ (ε * J) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num); push_cast; linarith
      _ = ((2 : ℝ) ^ ε) ^ J := by rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      _ ≤ (1 + ε) ^ J := by gcongr
  have := mul_le_mul_of_nonneg_right lower hc0.le
  linarith

/-! ### Dilation by a unit -/

lemma bohr_image_mul (Γ : Finset (ZMod N)) {u v : ZMod N} (huv : u * v = 1) (ρ : ℝ) :
    bohr (Γ.image (· * v)) ρ = (bohr Γ ρ).image (u * ·) := by
  ext x
  simp only [mem_bohr, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h
    refine ⟨v * x, fun γ hγ => ?_, ?_⟩
    · have := h γ hγ; rwa [mul_assoc] at this
    · rw [← mul_assoc, huv, one_mul]
  · rintro ⟨y, hy, rfl⟩ γ hγ
    have : γ * v * (u * y) = γ * y := by
      rw [mul_assoc, ← mul_assoc v, mul_comm v u, huv, one_mul]
    rw [this]; exact hy γ hγ

lemma card_bohr_image_mul (Γ : Finset (ZMod N)) {u v : ZMod N} (huv : u * v = 1) (ρ : ℝ) :
    (bohr (Γ.image (· * v)) ρ).card = (bohr Γ ρ).card := by
  rw [bohr_image_mul Γ huv, card_image_of_injective]
  intro a b hab
  have := congrArg (v * ·) hab
  simp only [← mul_assoc, mul_comm v u, huv, one_mul] at this
  exact this

lemma isReg_image_mul_iff (Γ : Finset (ZMod N)) {u v : ZMod N} (huv : u * v = 1) {ρ κ ε : ℝ} :
    IsReg (Γ.image (· * v)) ρ κ ε ↔ IsReg Γ ρ κ ε := by
  simp only [IsReg, card_bohr_image_mul Γ huv]

omit [NeZero N] in
lemma card_image_mul_le (Γ : Finset (ZMod N)) (v : ZMod N) : (Γ.image (· * v)).card ≤ Γ.card :=
  card_image_le

end

end KM

end KMFile_Bohr

section KMFile_Conv



/-!
# Convolutions and normalised indicator functions on a finite abelian group
-/

open Finset

namespace KM

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Indicator function of a finset. -/
def ind (S : Finset G) : G → ℝ := fun x => if x ∈ S then 1 else 0

/-- Uniform probability measure on a finset. -/
def mu (S : Finset G) : G → ℝ := fun x => if x ∈ S then (S.card : ℝ)⁻¹ else 0

/-- Convolution. -/
def conv (f g : G → ℝ) : G → ℝ := fun x => ∑ y, f y * g (x - y)

/-- Difference convolution `(f ○ g) x = ∑ y, f (x + y) g y`. -/
def dconv (f g : G → ℝ) : G → ℝ := fun x => ∑ y, f (x + y) * g y

/-- Translation. -/
def tr (t : G) (f : G → ℝ) : G → ℝ := fun x => f (x - t)

/-- Iterated convolution. -/
def iconv (f : G → ℝ) : ℕ → G → ℝ
  | 0 => ind {0}
  | k + 1 => conv f (iconv f k)

variable {S T A B : Finset G} {f g h : G → ℝ} {x y t : G}

@[simp] lemma ind_apply : ind S x = if x ∈ S then 1 else 0 := rfl
@[simp] lemma mu_apply : mu S x = if x ∈ S then (S.card : ℝ)⁻¹ else 0 := rfl

lemma ind_nonneg (S : Finset G) (x : G) : 0 ≤ ind S x := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (S : Finset G) (x : G) : ind S x ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

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

lemma sum_mul_ind (S : Finset G) (f : G → ℝ) : ∑ x, f x * ind S x = ∑ x ∈ S, f x := by
  unfold ind; simp [mul_ite, sum_ite_mem]

lemma sum_ind_mul (S : Finset G) (f : G → ℝ) : ∑ x, ind S x * f x = ∑ x ∈ S, f x := by
  simp_rw [mul_comm (ind S _)]; exact sum_mul_ind S f

lemma sum_mul_mu (S : Finset G) (f : G → ℝ) :
    ∑ x, f x * mu S x = (S.card : ℝ)⁻¹ * ∑ x ∈ S, f x := by
  rw [← sum_mul_ind S f, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  unfold mu ind; split_ifs <;> ring

lemma sum_mu_mul (S : Finset G) (f : G → ℝ) :
    ∑ x, mu S x * f x = (S.card : ℝ)⁻¹ * ∑ x ∈ S, f x := by
  simp_rw [mul_comm (mu S _)]; exact sum_mul_mu S f

lemma sum_sq_mu (hS : S.Nonempty) : ∑ x, mu S x ^ 2 = (S.card : ℝ)⁻¹ := by
  have : ∀ x, mu S x ^ 2 = mu S x * mu S x := fun x => sq _
  simp_rw [this, sum_mu_mul]
  have h2 : ∀ x ∈ S, mu S x = (S.card : ℝ)⁻¹ := fun x hx => by simp [hx]
  rw [sum_congr rfl h2, sum_const, nsmul_eq_mul]
  have : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  field_simp

/-! ### Reindexing -/

lemma sum_sub_right (f : G → ℝ) (t : G) : ∑ x, f (x - t) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.subRight t) _ _ (fun _ => rfl)

lemma sum_add_right (f : G → ℝ) (t : G) : ∑ x, f (x + t) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)

lemma sum_neg (f : G → ℝ) : ∑ x, f (-x) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.neg G) _ _ (fun _ => rfl)

lemma sum_sub_left (f : G → ℝ) (t : G) : ∑ x, f (t - x) = ∑ x, f x :=
  Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.addLeft t)) _ _
    (fun x => by simp [sub_eq_add_neg])

/-! ### Basic properties of convolutions -/

lemma conv_apply : conv f g x = ∑ y, f y * g (x - y) := rfl
lemma dconv_apply : dconv f g x = ∑ y, f (x + y) * g y := rfl
lemma tr_apply : tr t f x = f (x - t) := rfl

lemma conv_comm (f g : G → ℝ) : conv f g = conv g f := by
  ext x; unfold conv
  rw [← sum_sub_left _ x]
  congr 1; ext y; rw [sub_sub_cancel, mul_comm]

lemma sum_conv (f g : G → ℝ) : ∑ x, conv f g x = (∑ x, f x) * ∑ x, g x := by
  unfold conv
  rw [sum_comm]
  simp_rw [← mul_sum]
  simp_rw [sum_sub_right (fun x => g x)]
  rw [sum_mul]

lemma sum_dconv (f g : G → ℝ) : ∑ x, dconv f g x = (∑ x, f x) * ∑ x, g x := by
  unfold dconv
  rw [sum_comm]
  simp_rw [← sum_mul]
  simp_rw [sum_add_right (fun x => f x)]
  rw [mul_sum]

lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ conv f g := fun x =>
  sum_nonneg fun y _ => mul_nonneg (hf y) (hg _)

lemma dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ dconv f g := fun x =>
  sum_nonneg fun y _ => mul_nonneg (hf _) (hg y)

lemma mu_nonneg' (S : Finset G) : 0 ≤ mu S := fun x => mu_nonneg S x

lemma ind_nonneg' (S : Finset G) : 0 ≤ ind S := fun x => ind_nonneg S x

lemma dconv_eq_conv_neg (f g : G → ℝ) : dconv f g = conv f (fun x => g (-x)) := by
  ext x; unfold dconv conv
  rw [← sum_sub_right _ x]
  congr 1; ext y; simp

lemma conv_assoc (f g h : G → ℝ) : conv (conv f g) h = conv f (conv g h) := by
  ext x; unfold conv
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← sum_add_right _ z]
  refine sum_congr rfl fun w _ => ?_
  simp only [add_sub_cancel_right]
  rw [show x - (w + z) = x - z - w by abel]; ring

lemma conv_add (f g h : G → ℝ) : conv f (g + h) = conv f g + conv f h := by
  ext x; simp [conv, mul_add, sum_add_distrib]

lemma add_conv (f g h : G → ℝ) : conv (f + g) h = conv f h + conv g h := by
  ext x; simp [conv, add_mul, sum_add_distrib]

lemma conv_sub (f g h : G → ℝ) : conv f (g - h) = conv f g - conv f h := by
  ext x; simp [conv, mul_sub, sum_sub_distrib]

lemma sub_conv (f g h : G → ℝ) : conv (f - g) h = conv f h - conv g h := by
  ext x; simp [conv, sub_mul, sum_sub_distrib]

lemma dconv_sub (f g h : G → ℝ) : dconv f (g - h) = dconv f g - dconv f h := by
  ext x; simp [dconv, mul_sub, sum_sub_distrib]

lemma sub_dconv (f g h : G → ℝ) : dconv (f - g) h = dconv f h - dconv g h := by
  ext x; simp [dconv, sub_mul, sum_sub_distrib]

lemma conv_ind_zero (f : G → ℝ) : conv f (ind {0}) = f := by
  ext x; unfold conv ind
  simp only [mem_singleton, sub_eq_zero, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]; simp

lemma ind_zero_conv (f : G → ℝ) : conv (ind {0}) f = f := by
  rw [conv_comm, conv_ind_zero]

/-- Inner product of a convolution with a function. -/
lemma sum_conv_mul (f g h : G → ℝ) :
    ∑ x, conv f g x * h x = ∑ y, f y * ∑ x, g x * h (x + y) := by
  unfold conv
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum, ← sum_add_right _ y]
  refine sum_congr rfl fun x _ => ?_
  rw [add_sub_cancel_right]; ring

lemma sum_iconv (hf : ∑ x, f x = 1) (k : ℕ) : ∑ x, iconv f k x = 1 := by
  induction k with
  | zero => rw [show iconv f 0 = ind {0} from rfl, sum_ind]; norm_num
  | succ k ih => rw [iconv, sum_conv, hf, ih, one_mul]

lemma iconv_nonneg (hf : 0 ≤ f) (k : ℕ) : 0 ≤ iconv f k := by
  induction k with
  | zero => exact ind_nonneg' _
  | succ k ih => exact conv_nonneg hf ih

/-! ### Translates of indicator functions -/

lemma ind_sub_eq (S : Finset G) (x t : G) : ind S (x - t) = ind (S.image (· + t)) x := by
  unfold ind
  congr 1
  apply propext
  simp only [mem_image]
  constructor
  · intro h; exact ⟨x - t, h, sub_add_cancel x t⟩
  · rintro ⟨y, hy, rfl⟩; simpa using hy

end

end KM

end KMFile_Conv

section KMFile_Reg



/-!
# Consequences of regularity of Bohr sets
-/

open Finset
open scoped Pointwise

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N] {Γ : Finset (ZMod N)} {ρ κ ε : ℝ}

/-- A function supported on a Bohr set. -/
def SuppIn (f : ZMod N → ℝ) (Γ : Finset (ZMod N)) (r : ℝ) : Prop := ∀ x, f x ≠ 0 → x ∈ bohr Γ r

lemma suppIn_mu {r : ℝ} : SuppIn (mu (bohr Γ r)) Γ r := by
  intro x hx; by_contra h; exact hx (by simp [mu_apply, h])

lemma SuppIn.conv {f g : ZMod N → ℝ} {r r' : ℝ} (hf : SuppIn f Γ r) (hg : SuppIn g Γ r') :
    SuppIn (conv f g) Γ (r + r') := by
  intro x hx
  obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero hx
  have h1 : f y ≠ 0 := left_ne_zero_of_mul hy
  have h2 : g (x - y) ≠ 0 := right_ne_zero_of_mul hy
  have := add_mem_bohr (hf y h1) (hg _ h2)
  rwa [add_sub_cancel] at this

lemma SuppIn.mono {f : ZMod N → ℝ} {r r' : ℝ} (hf : SuppIn f Γ r) (h : r ≤ r') : SuppIn f Γ r' :=
  fun x hx => bohr_mono h (hf x hx)

lemma suppIn_iconv_mu {r : ℝ} (hr : 0 ≤ r) (L : ℕ) : SuppIn (iconv (mu (bohr Γ r)) L) Γ (L * r) := by
  induction L with
  | zero =>
    intro x hx
    simp only [iconv, ind_apply, mem_singleton, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not] at hx
    subst hx; simp
  | succ L ih =>
    have := suppIn_mu.conv ih (Γ := Γ) (r := r)
    refine this.mono (le_of_eq ?_)
    push_cast; ring

/-- Translating a regular Bohr set by a small element changes the uniform measure little. -/
lemma IsReg.sum_abs_translate_le (h : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    {t : ZMod N} (ht : t ∈ bohr Γ (κ * ρ)) :
    ∑ x, |mu (bohr Γ ρ) (x - t) - mu (bohr Γ ρ) x| ≤ 2 * ε := by
  set B := bohr Γ ρ with hB
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast bohr_card_pos hρ
  set S1 := B.filter (fun x => x - t ∉ B) with hS1
  set S2 := B.filter (fun x => x - (-t) ∉ B) with hS2
  have h1 : (S1.card : ℝ) ≤ ε * B.card := h.card_sdiff_le hρ hκ hε ht
  have h2 : (S2.card : ℝ) ≤ ε * B.card := h.card_sdiff_le hρ hκ hε (neg_mem_bohr ht)
  have hm1 : ∀ x, x ∈ S1 ↔ x ∈ B ∧ x - t ∉ B := fun x => by rw [hS1, mem_filter]
  have hm2 : ∀ x, x ∈ S2.image (· + t) ↔ x - t ∈ B ∧ x ∉ B := by
    intro x
    rw [mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hS2, mem_filter, sub_neg_eq_add] at ha
      simpa using ha
    · rintro ⟨h1, h2⟩
      refine ⟨x - t, ?_, by abel⟩
      rw [hS2, mem_filter, sub_neg_eq_add, sub_add_cancel]
      exact ⟨h1, h2⟩
  have hpt : ∀ x, |mu B (x - t) - mu B x| ≤ (B.card : ℝ)⁻¹ * (ind S1 x + ind (S2.image (· + t)) x) := by
    intro x
    have hinv : (0:ℝ) ≤ (B.card : ℝ)⁻¹ := by positivity
    by_cases hx : x ∈ B <;> by_cases hxt : x - t ∈ B
    · simp [mu_apply, hx, hxt]; positivity
    · have h1 : x ∈ S1 := (hm1 x).2 ⟨hx, hxt⟩
      have h2 : x ∉ S2.image (· + t) := fun h => hxt ((hm2 x).1 h).1
      rw [ind_apply, ind_apply, if_pos h1, if_neg h2, mu_apply, mu_apply, if_pos hx, if_neg hxt]
      simp
    · have h1 : x ∉ S1 := fun h => hx ((hm1 x).1 h).1
      have h2 : x ∈ S2.image (· + t) := (hm2 x).2 ⟨hxt, hx⟩
      rw [ind_apply, ind_apply, if_neg h1, if_pos h2, mu_apply, mu_apply, if_neg hx, if_pos hxt]
      simp
    · simp [mu_apply, hx, hxt]; positivity
  calc ∑ x, |mu B (x - t) - mu B x|
      ≤ ∑ x, (B.card : ℝ)⁻¹ * (ind S1 x + ind (S2.image (· + t)) x) := sum_le_sum fun x _ => hpt x
    _ = (B.card : ℝ)⁻¹ * (S1.card + S2.card) := by
        rw [← mul_sum, sum_add_distrib, sum_ind, sum_ind, card_image_of_injective _ (add_left_injective t)]
    _ ≤ (B.card : ℝ)⁻¹ * (ε * B.card + ε * B.card) := by gcongr
    _ = 2 * ε := by field_simp; ring

/-- A regular Bohr set's uniform measure is dominated by a smoothed version. -/
lemma IsReg.mu_le_conv (h : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    {ν : ZMod N → ℝ} (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (hsupp : SuppIn ν Γ (κ * ρ))
    (x : ZMod N) :
    mu (bohr Γ ρ) x ≤ (1 + ε) * conv ν (mu (bohr Γ (ρ * (1 + κ)))) x := by
  set B := bohr Γ ρ
  set B' := bohr Γ (ρ * (1 + κ))
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast bohr_card_pos hρ
  have hB'c : (0 : ℝ) < B'.card := by exact_mod_cast bohr_card_pos (by positivity)
  have hconv0 : 0 ≤ conv ν (mu B') x := conv_nonneg hν (mu_nonneg' B') x
  by_cases hx : x ∈ B
  · have hval : conv ν (mu B') x = (B'.card : ℝ)⁻¹ := by
      rw [conv_apply]
      calc ∑ y, ν y * mu B' (x - y) = ∑ y, ν y * (B'.card : ℝ)⁻¹ := by
            refine sum_congr rfl fun y _ => ?_
            by_cases hy : ν y = 0
            · simp [hy]
            · have hy' := hsupp y hy
              have : x - y ∈ B' := by
                have := sub_mem_bohr hx hy'
                exact bohr_mono (le_of_eq (by ring)) this
              simp [mu_apply, this]
        _ = (B'.card : ℝ)⁻¹ := by rw [← sum_mul, hν1, one_mul]
    rw [hval, mu_apply, if_pos hx]
    have hup := h.card_upper hρ hκ hε
    rw [inv_le_iff_one_le_mul₀ hBc]
    calc (1 : ℝ) = B'.card * (B'.card : ℝ)⁻¹ := by field_simp
      _ ≤ ((1 + ε) * B.card) * (B'.card : ℝ)⁻¹ := by gcongr
      _ = (1 + ε) * (B'.card : ℝ)⁻¹ * B.card := by ring
  · rw [mu_apply, if_neg hx]; positivity

/-- Adding a small Bohr set barely enlarges a regular Bohr set. -/
lemma IsReg.card_add_le (h : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    {S : Finset (ZMod N)} (hS : S ⊆ bohr Γ (κ * ρ)) :
    ((bohr Γ ρ + S).card : ℝ) ≤ (1 + ε) * (bohr Γ ρ).card := by
  have hsub : bohr Γ ρ + S ⊆ bohr Γ (ρ * (1 + κ)) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
    exact bohr_mono (le_of_eq (by ring)) (add_mem_bohr hx (hS hy))
  calc ((bohr Γ ρ + S).card : ℝ) ≤ (bohr Γ (ρ * (1 + κ))).card := by exact_mod_cast card_le_card hsub
    _ ≤ _ := h.card_upper hρ hκ hε

end

end KM

end KMFile_Reg

section KMFile_Bour



/-!
# Bourgain's narrowing lemma (Bloom–Sisask Lemma bour)
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The relative density of `A` on the translate `x + B`. -/
def relDens (A B : Finset (ZMod N)) (x : ZMod N) : ℝ :=
  ((A.filter fun a => a - x ∈ B).card : ℝ) / B.card

lemma relDens_nonneg (A B : Finset (ZMod N)) (x : ZMod N) : 0 ≤ relDens A B x := by
  unfold relDens; positivity

/-- Averaging the relative density over a regular Bohr set. -/
lemma avg_relDens_ge {Γ : Finset (ZMod N)} {ρ κ ε : ℝ} (hreg : IsReg Γ ρ κ ε) (hρ : 0 < ρ)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {A : Finset (ZMod N)} (hA : A ⊆ bohr Γ ρ) {B' : Finset (ZMod N)}
    (hB' : B'.Nonempty) (hB'sub : B' ⊆ bohr Γ (κ * ρ)) :
    ((A.card : ℝ) - ε * (bohr Γ ρ).card) / (bohr Γ ρ).card ≤
      ∑ x, mu (bohr Γ ρ) x * relDens A B' x := by
  set B := bohr Γ ρ with hB
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast bohr_card_pos hρ.le
  have hB'c : (0 : ℝ) < B'.card := by exact_mod_cast hB'.card_pos
  -- double counting
  have hdc : ∑ x ∈ B, ((A.filter fun a => a - x ∈ B').card : ℝ) =
      ∑ z ∈ B', ((A.filter fun a => a - z ∈ B).card : ℝ) := by
    have h1 : ∀ x, ((A.filter fun a => a - x ∈ B').card : ℝ) = ∑ a ∈ A, ind B' (a - x) := by
      intro x; rw [card_filter]; push_cast; rfl
    have h2 : ∀ z, ((A.filter fun a => a - z ∈ B).card : ℝ) = ∑ a ∈ A, ind B (a - z) := by
      intro z; rw [card_filter]; push_cast; rfl
    simp_rw [h1, h2]
    rw [sum_comm, sum_comm (s := B')]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_ind_mul B, ← sum_ind_mul B']
    exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun x => by
      simp only [Equiv.subLeft_apply, sub_sub_cancel]; ring)
  have hlow : ∀ z ∈ B', (A.card : ℝ) - ε * B.card ≤ ((A.filter fun a => a - z ∈ B).card : ℝ) := by
    intro z hz
    have hs := hreg.card_sdiff_le hρ.le hκ hε (hB'sub hz)
    have hsub : A.filter (fun a => a - z ∉ B) ⊆ B.filter (fun x => x - z ∉ B) := by
      intro a ha; rw [mem_filter] at *; exact ⟨hA ha.1, ha.2⟩
    have h1 : ((A.filter fun a => a - z ∉ B).card : ℝ) ≤ ε * B.card :=
      le_trans (by exact_mod_cast card_le_card hsub) hs
    have h2 := card_filter_add_card_filter_not (s := A) (fun a => a - z ∈ B)
    have : ((A.filter fun a => a - z ∈ B).card : ℝ) + (A.filter fun a => a - z ∉ B).card = A.card := by
      exact_mod_cast h2
    linarith
  have e : ∑ x, mu B x * relDens A B' x =
      ((B.card : ℝ) * B'.card)⁻¹ * ∑ x ∈ B, ((A.filter fun a => a - x ∈ B').card : ℝ) := by
    rw [sum_mu_mul, mul_sum, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    unfold relDens; field_simp
  rw [e, hdc]
  calc ((A.card : ℝ) - ε * B.card) / B.card
      = ((B.card : ℝ) * B'.card)⁻¹ * ∑ z ∈ B', ((A.card : ℝ) - ε * B.card) := by
        rw [sum_const, nsmul_eq_mul]; field_simp
    _ ≤ _ := by gcongr with z hz; exact hlow z hz

/-- **Bourgain's narrowing lemma.** Either `A` has increased density on a translate of one of two
smaller Bohr sets, or some translate has almost the right density on both. -/
theorem bour {Γ : Finset (ZMod N)} {ρ κ ε : ℝ} (hreg : IsReg Γ ρ κ ε) (hρ : 0 < ρ)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {A : Finset (ZMod N)} (hA : A ⊆ bohr Γ ρ) {α : ℝ}
    (hα : α * (bohr Γ ρ).card ≤ A.card) {B₁ B₂ : Finset (ZMod N)} (hB₁ : B₁.Nonempty)
    (hB₂ : B₂.Nonempty) (hB₁sub : B₁ ⊆ bohr Γ (κ * ρ)) (hB₂sub : B₂ ⊆ bohr Γ (κ * ρ)) {θ : ℝ}
    (hθ : 2 * ε ≤ θ * α) :
    (∃ x, (1 + θ) * α ≤ relDens A B₁ x) ∨ (∃ x, (1 + θ) * α ≤ relDens A B₂ x) ∨
      (∃ x, (1 - 2 * θ) * α ≤ relDens A B₁ x ∧ (1 - 2 * θ) * α ≤ relDens A B₂ x) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  set B := bohr Γ ρ
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast bohr_card_pos hρ.le
  have hBne : B.Nonempty := bohr_nonempty hρ.le
  have a1 := avg_relDens_ge hreg hρ hκ hε hA hB₁ hB₁sub
  have a2 := avg_relDens_ge hreg hρ hκ hε hA hB₂ hB₂sub
  have hαε : α - ε ≤ ((A.card : ℝ) - ε * B.card) / B.card := by
    rw [le_div_iff₀ hBc]; linarith
  -- sharpen: strict inequality in `hpt`
  have hpt' : ∀ x, relDens A B₁ x + relDens A B₂ x < (2 - θ) * α := by
    intro x
    by_cases hx : (1 - 2 * θ) * α ≤ relDens A B₁ x
    · have := h3 x hx; have := h1 x; linarith
    · push_neg at hx; have := h2 x; linarith
  have hsum : ∑ x, mu B x * (relDens A B₁ x + relDens A B₂ x) < (2 - θ) * α := by
    obtain ⟨x0, hx0⟩ := id hBne
    calc ∑ x, mu B x * (relDens A B₁ x + relDens A B₂ x) < ∑ x, mu B x * ((2 - θ) * α) := by
          refine sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left (hpt' x).le (mu_nonneg B x))
            ⟨x0, mem_univ _, ?_⟩
          have : 0 < mu B x0 := by simp [mu_apply, hx0, hBc]
          exact mul_lt_mul_of_pos_left (hpt' x0) this
      _ = (2 - θ) * α := by rw [← sum_mul, sum_mu hBne, one_mul]
  simp only [mul_add, sum_add_distrib] at hsum
  linarith

end

end KM

end KMFile_Bour

section KMFile_CSMoment



/-! # Moment bound for sums of independent samples (used in Croot–Sisask) -/

open Finset

namespace KM

noncomputable section

/-- AM–GM in the form `|∏ y| ≤ (∑ |y|^n)/n`. -/
lemma abs_prod_le_sum_pow_div {n : ℕ} (hn : 1 ≤ n) (y : Fin n → ℝ) :
    |∏ l, y l| ≤ (∑ l, |y l| ^ n) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h := Real.geom_mean_le_arith_mean_weighted univ (fun _ => (1 : ℝ) / n)
    (fun l => |y l| ^ n) (fun _ _ => by positivity)
    (by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
    (fun _ _ => by positivity)
  have e : ∀ l, (|y l| ^ n) ^ ((1 : ℝ) / n) = |y l| := by
    intro l
    rw [one_div, Real.pow_rpow_inv_natCast (abs_nonneg _) (by omega)]
  simp only [e] at h
  rw [abs_prod, ← mul_sum] at *
  calc ∏ l, |y l| ≤ 1 / n * ∑ l, |y l| ^ n := h
    _ = (∑ l, |y l| ^ n) / n := by ring

variable {ι : Type*}

lemma sum_piFinset_apply (A : Finset ι) {m : ℕ} (i : Fin m) (F : ι → ℝ) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), F (a i) = (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, F b := by
  have h1 : ∀ a : Fin m → ι, F (a i) = ∏ i', (if i' = i then F (a i') else 1) := by
    intro a; rw [prod_ite_eq']; simp
  simp_rw [h1]
  rw [← prod_univ_sum (t := fun _ => A) (f := fun i' b => if i' = i then F b else 1)]
  have h2 : ∀ i', (∑ b ∈ A, (if i' = i then F b else 1)) =
      if i' = i then ∑ b ∈ A, F b else (A.card : ℝ) := by
    intro i'; split_ifs <;> simp
  simp_rw [h2]
  rw [← mul_prod_erase univ _ (mem_univ i), if_pos rfl]
  rw [prod_congr rfl (fun i' hi' => if_neg (ne_of_mem_erase hi')), prod_const, card_erase_of_mem
    (mem_univ i), card_univ, Fintype.card_fin]
  ring

/-- Multiplicity of `i` in `j`. -/
def mult {n m : ℕ} (j : Fin n → Fin m) (i : Fin m) : ℕ := (univ.filter fun l => j l = i).card

lemma sum_piFinset_prod_eq (A : Finset ι) (g : ι → ℝ) {n m : ℕ} (j : Fin n → Fin m) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), ∏ l, g (a (j l)) =
      ∏ i, ∑ b ∈ A, g b ^ mult j i := by
  rw [prod_univ_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [← prod_fiberwise univ j (fun l => g (a (j l)))]
  refine prod_congr rfl fun i _ => ?_
  rw [prod_congr rfl (fun l hl => by rw [(mem_filter.1 hl).2]), prod_const]
  rfl

lemma sum_piFinset_prod_eq_zero (A : Finset ι) (g : ι → ℝ) (hg : ∑ b ∈ A, g b = 0) {n m : ℕ}
    (j : Fin n → Fin m) (h : ∃ i, mult j i = 1) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), ∏ l, g (a (j l)) = 0 := by
  rw [sum_piFinset_prod_eq]
  obtain ⟨i, hi⟩ := h
  exact prod_eq_zero (mem_univ i) (by rw [hi]; simpa using hg)

lemma abs_sum_piFinset_prod_le (A : Finset ι) (g : ι → ℝ) {r m : ℕ} (hr : 1 ≤ r)
    (j : Fin (2 * r) → Fin m) :
    |∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), ∏ l, g (a (j l))| ≤
      (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, g b ^ (2 * r) := by
  have hev : Even (2 * r) := even_two_mul r
  calc |∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), ∏ l, g (a (j l))|
      ≤ ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), |∏ l, g (a (j l))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), (∑ l, |g (a (j l))| ^ (2 * r)) / (2 * r : ℕ) :=
        sum_le_sum fun a _ => abs_prod_le_sum_pow_div (by omega) _
    _ = (∑ l, ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), g (a (j l)) ^ (2 * r)) / (2 * r : ℕ) := by
        rw [← sum_div, sum_comm]
        simp_rw [hev.pow_abs]
    _ = (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, g b ^ (2 * r) := by
        simp_rw [sum_piFinset_apply A _ (fun b => g b ^ (2 * r))]
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : ((2 * r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 2 * r ≠ 0)
        field_simp

lemma card_image_le_of_mult {r m : ℕ} (j : Fin (2 * r) → Fin m) (h : ∀ i, mult j i ≠ 1) :
    (univ.image j).card ≤ r := by
  have hsum : ∑ i ∈ univ.image j, mult j i = 2 * r := by
    unfold mult
    rw [← card_eq_sum_card_image]; simp
  have h2 : ∀ i ∈ univ.image j, 2 ≤ mult j i := by
    intro i hi
    obtain ⟨l, -, rfl⟩ := mem_image.1 hi
    have h1 : 1 ≤ mult j (j l) := card_pos.2 ⟨l, by simp⟩
    have := h (j l); omega
  have := sum_le_sum h2
  rw [sum_const, smul_eq_mul, hsum] at this
  omega

lemma card_bad_le {r m : ℕ} (hr : 1 ≤ r) :
    ((univ.filter fun j : Fin (2 * r) → Fin m => ∀ i, mult j i ≠ 1).card : ℝ) ≤
      (m : ℝ) ^ r * (r : ℝ) ^ (2 * r) := by
  have hsub : (univ.filter fun j : Fin (2 * r) → Fin m => ∀ i, mult j i ≠ 1) ⊆
      (univ : Finset ((Fin r → Fin m) × (Fin (2 * r) → Fin r))).image (fun p => p.1 ∘ p.2) := by
    intro j hj
    have hk := card_image_le_of_mult j (mem_filter.1 hj).2
    set I := univ.image j with hI
    set k := I.card
    let e := I.equivFin
    have hmem : ∀ l, j l ∈ I := fun l => mem_image_of_mem _ (mem_univ l)
    let σ : Fin (2 * r) → Fin r := fun l => Fin.castLE hk (e ⟨j l, hmem l⟩)
    let u : Fin r → Fin m := fun t =>
      if ht : t.1 < k then (e.symm ⟨t.1, ht⟩).1 else j ⟨0, by omega⟩
    refine mem_image.2 ⟨(u, σ), mem_univ _, ?_⟩
    funext l
    simp only [Function.comp_apply, u, σ, Fin.val_castLE, Fin.is_lt, dite_true]
    simp
  calc ((univ.filter fun j : Fin (2 * r) → Fin m => ∀ i, mult j i ≠ 1).card : ℝ)
      ≤ ((univ : Finset ((Fin r → Fin m) × (Fin (2 * r) → Fin r))).image
          (fun p => p.1 ∘ p.2)).card := by exact_mod_cast card_le_card hsub
    _ ≤ (univ : Finset ((Fin r → Fin m) × (Fin (2 * r) → Fin r))).card := by
        exact_mod_cast card_image_le
    _ = (m : ℝ) ^ r * (r : ℝ) ^ (2 * r) := by
        simp [Fintype.card_prod]

/-- Moment bound for sums of independent mean-zero samples. -/
theorem moment_bound (A : Finset ι) (g : ι → ℝ) (hg : ∑ b ∈ A, g b = 0) {r : ℕ} (hr : 1 ≤ r)
    (m : ℕ) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), (∑ i, g (a i)) ^ (2 * r) ≤
      (m : ℝ) ^ r * (r : ℝ) ^ (2 * r) * ((A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, g b ^ (2 * r)) := by
  have hexp : ∀ a : Fin m → ι, (∑ i, g (a i)) ^ (2 * r) =
      ∑ j : Fin (2 * r) → Fin m, ∏ l, g (a (j l)) := by
    intro a; rw [← Fin.prod_const, Fintype.prod_sum]
  simp_rw [hexp]
  rw [sum_comm]
  rw [← sum_filter_add_sum_filter_not univ (fun j : Fin (2 * r) → Fin m => ∀ i, mult j i ≠ 1)]
  have hz : ∑ j ∈ univ.filter (fun j : Fin (2 * r) → Fin m => ¬ ∀ i, mult j i ≠ 1),
      ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), ∏ l, g (a (j l)) = 0 := by
    refine sum_eq_zero fun j hj => ?_
    have := (mem_filter.1 hj).2
    push_neg at this
    exact sum_piFinset_prod_eq_zero A g hg j this
  rw [hz, add_zero]
  have hB : 0 ≤ (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, g b ^ (2 * r) := by
    have : ∀ b ∈ A, 0 ≤ g b ^ (2 * r) := fun b _ => (even_two_mul r).pow_nonneg _
    have := sum_nonneg this; positivity
  calc ∑ j ∈ univ.filter (fun j : Fin (2 * r) → Fin m => ∀ i, mult j i ≠ 1),
        ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), ∏ l, g (a (j l))
      ≤ ∑ j ∈ univ.filter (fun j : Fin (2 * r) → Fin m => ∀ i, mult j i ≠ 1),
          (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, g b ^ (2 * r) :=
        sum_le_sum fun j _ => (le_abs_self _).trans (abs_sum_piFinset_prod_le A g hr j)
    _ = _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_bad_le hr) hB

end

end KM

end KMFile_CSMoment

section KMFile_CrootSisask



/-!
# Croot–Sisask almost periodicity (moment version)
-/

open Finset
open scoped Pointwise

namespace KM

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Sample size in the Croot–Sisask lemma. -/
def csM (r : ℕ) (ε : ℝ) : ℕ := ⌈32 * (r : ℝ) ^ 2 / ε ^ 2⌉₊

/-- Empirical average along a sample. -/
def samp {m : ℕ} (f : G → ℝ) (a : Fin m → G) (x : G) : ℝ := (m : ℝ)⁻¹ * ∑ i, f (x - a i)

lemma conv_mu_eq (A : Finset G) (f : G → ℝ) (x : G) :
    conv (mu A) f x = (A.card : ℝ)⁻¹ * ∑ b ∈ A, f (x - b) := by
  rw [conv_apply, sum_mu_mul]

/-- The pointwise moment estimate for the empirical average. -/
lemma sum_samp_sub_pow_le {A : Finset G} (hA : A.Nonempty) {f : G → ℝ} (hf : ∀ x, 0 ≤ f x)
    {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (x : G) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), (samp f a x - conv (mu A) f x) ^ (2 * r) ≤
      (4 * (r : ℝ) ^ 2 / m) ^ r * (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, f (x - b) ^ (2 * r) := by
  set ψ := conv (mu A) f x with hψ
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  let g : G → ℝ := fun b => f (x - b) - ψ
  have hg : ∑ b ∈ A, g b = 0 := by
    simp only [g, sum_sub_distrib, sum_const, nsmul_eq_mul, hψ, conv_mu_eq]
    field_simp; ring
  have hsamp : ∀ a : Fin m → G, samp f a x - ψ = (m : ℝ)⁻¹ * ∑ i, g (a i) := by
    intro a
    simp only [samp, g, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hψ0 : 0 ≤ ψ := by
    rw [hψ, conv_mu_eq]; exact mul_nonneg (by positivity) (sum_nonneg fun b _ => hf _)
  have hg2 : ∑ b ∈ A, g b ^ (2 * r) ≤ 4 ^ r * ∑ b ∈ A, f (x - b) ^ (2 * r) := by
    have hJ : (A.card : ℝ) * ψ ^ (2 * r) ≤ ∑ b ∈ A, f (x - b) ^ (2 * r) := by
      have := Real.pow_arith_mean_le_arith_mean_pow A (fun _ => (A.card : ℝ)⁻¹)
        (fun b => f (x - b)) (fun _ _ => by positivity)
        (by rw [sum_const, nsmul_eq_mul]; field_simp) (fun _ _ => hf _) (2 * r)
      rw [← mul_sum, ← mul_sum, ← conv_mu_eq, ← hψ] at this
      calc (A.card : ℝ) * ψ ^ (2 * r) ≤ A.card * ((A.card : ℝ)⁻¹ *
            ∑ b ∈ A, f (x - b) ^ (2 * r)) := by gcongr
        _ = _ := by field_simp
    have hpt : ∀ b ∈ A, g b ^ (2 * r) ≤ 2 ^ (2 * r - 1) * (f (x - b) ^ (2 * r) + ψ ^ (2 * r)) := by
      intro b _
      have := Even.add_pow_le (a := f (x - b)) (b := -ψ) (n := 2 * r) (even_two_mul r)
      rwa [Even.neg_pow (even_two_mul r)] at this
    calc ∑ b ∈ A, g b ^ (2 * r) ≤ ∑ b ∈ A, 2 ^ (2 * r - 1) * (f (x - b) ^ (2 * r) + ψ ^ (2 * r)) :=
          sum_le_sum hpt
      _ = 2 ^ (2 * r - 1) * (∑ b ∈ A, f (x - b) ^ (2 * r) + A.card * ψ ^ (2 * r)) := by
          rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ (2 * r - 1) * (2 * ∑ b ∈ A, f (x - b) ^ (2 * r)) := by gcongr; linarith
      _ = 4 ^ r * ∑ b ∈ A, f (x - b) ^ (2 * r) := by
          rw [← mul_assoc, ← pow_succ, show 2 * r - 1 + 1 = 2 * r by omega, pow_mul]; norm_num
  have hmom := moment_bound A g hg hr m
  calc ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), (samp f a x - ψ) ^ (2 * r)
      = ((m : ℝ)⁻¹) ^ (2 * r) * ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A),
          (∑ i, g (a i)) ^ (2 * r) := by
        rw [mul_sum]; refine sum_congr rfl fun a _ => ?_; rw [hsamp, mul_pow]
    _ ≤ ((m : ℝ)⁻¹) ^ (2 * r) * ((m : ℝ) ^ r * (r : ℝ) ^ (2 * r) *
          ((A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, g b ^ (2 * r))) := by gcongr
    _ ≤ ((m : ℝ)⁻¹) ^ (2 * r) * ((m : ℝ) ^ r * (r : ℝ) ^ (2 * r) *
          ((A.card : ℝ) ^ (m - 1) * (4 ^ r * ∑ b ∈ A, f (x - b) ^ (2 * r)))) := by gcongr
    _ = (4 * (r : ℝ) ^ 2 / m) ^ r * (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, f (x - b) ^ (2 * r) := by
        have e1 : ((m:ℝ)⁻¹) ^ (2 * r) * (m:ℝ) ^ r = ((m:ℝ)⁻¹) ^ r := by
          rw [two_mul, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hm0.ne', one_pow, mul_one]
        have e2 : (4 * (r:ℝ) ^ 2 / m) ^ r = 4 ^ r * (r:ℝ) ^ (2 * r) * ((m:ℝ)⁻¹) ^ r := by
          rw [div_eq_mul_inv, mul_pow, mul_pow, ← pow_mul]
        calc ((m:ℝ)⁻¹) ^ (2 * r) * ((m : ℝ) ^ r * (r : ℝ) ^ (2 * r) *
              ((A.card : ℝ) ^ (m - 1) * (4 ^ r * ∑ b ∈ A, f (x - b) ^ (2 * r))))
            = (((m:ℝ)⁻¹) ^ (2 * r) * (m:ℝ) ^ r) * (r : ℝ) ^ (2 * r) * 4 ^ r *
              (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, f (x - b) ^ (2 * r) := by ring
          _ = _ := by rw [e1, e2]; ring

/-- Total moment estimate. -/
lemma sum_sum_samp_sub_pow_le {A : Finset G} (hA : A.Nonempty) {f : G → ℝ} (hf : ∀ x, 0 ≤ f x)
    {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), ∑ x, (samp f a x - conv (mu A) f x) ^ (2 * r) ≤
      (A.card : ℝ) ^ m * ((4 * (r : ℝ) ^ 2 / m) ^ r * ∑ x, f x ^ (2 * r)) := by
  rw [sum_comm]
  calc ∑ x, ∑ a ∈ Fintype.piFinset (fun _ : Fin m => A), (samp f a x - conv (mu A) f x) ^ (2 * r)
      ≤ ∑ x, (4 * (r : ℝ) ^ 2 / m) ^ r * (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, f (x - b) ^ (2 * r) :=
        sum_le_sum fun x _ => sum_samp_sub_pow_le hA hf hr hm x
    _ = (4 * (r : ℝ) ^ 2 / m) ^ r * (A.card : ℝ) ^ (m - 1) * ∑ b ∈ A, ∑ x, f (x - b) ^ (2 * r) := by
        rw [← mul_sum, sum_comm]
    _ = (4 * (r : ℝ) ^ 2 / m) ^ r * (A.card : ℝ) ^ (m - 1) * (A.card * ∑ x, f x ^ (2 * r)) := by
        congr 1
        rw [sum_congr rfl (fun b _ => sum_sub_right (fun x => f x ^ (2 * r)) b), sum_const,
          nsmul_eq_mul]
    _ = (A.card : ℝ) ^ m * ((4 * (r : ℝ) ^ 2 / m) ^ r * ∑ x, f x ^ (2 * r)) := by
        have : (A.card : ℝ) ^ m = (A.card : ℝ) ^ (m - 1) * A.card := by
          rw [← pow_succ]; congr 1; omega
        rw [this]; ring

lemma samp_sub_const {m : ℕ} (f : G → ℝ) (c : Fin m → G) (t x : G) :
    samp f (c - fun _ => t) x = samp f c (x + t) := by
  unfold samp; congr 1; refine sum_congr rfl fun i _ => ?_; congr 1; simp; abel

/-- **Croot–Sisask** `L^{2r}` almost periodicity. -/
theorem croot_sisask {A Y : Finset G} (hA : A.Nonempty) (hY : Y.Nonempty) {K : ℝ}
    (hK : ((A + Y).card : ℝ) ≤ K * A.card) {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) {r : ℕ} (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T ⊆ Y, (Y.card : ℝ) / (2 * K ^ csM r ε) ≤ T.card ∧ ∀ t₁ ∈ T, ∀ t₂ ∈ T,
      ∑ x, (conv (mu A) f (x + (t₁ - t₂)) - conv (mu A) f x) ^ (2 * r) ≤
        ε ^ (2 * r) * ∑ x, f x ^ (2 * r) := by
  set m := csM r ε with hm_def
  have hm1 : 1 ≤ m := by
    rw [hm_def, csM, Nat.one_le_ceil_iff]; have : (0:ℝ) < r := by exact_mod_cast hr
    positivity
  have hmge : 32 * (r : ℝ) ^ 2 / ε ^ 2 ≤ m := Nat.le_ceil _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  set ψ := conv (mu A) f with hψ
  set E := (4 * (r : ℝ) ^ 2 / m) ^ r * ∑ x, f x ^ (2 * r) with hE
  have hF0 : ∀ x, 0 ≤ f x ^ (2 * r) := fun x => (even_two_mul r).pow_nonneg _
  have hE0 : 0 ≤ E := by have := sum_nonneg fun x (_ : x ∈ univ) => hF0 x; positivity
  set F : (Fin m → G) → ℝ := fun a => ∑ x, (samp f a x - ψ x) ^ (2 * r) with hF
  have hFnn : ∀ a, 0 ≤ F a := fun a => sum_nonneg fun x _ => (even_two_mul r).pow_nonneg _
  set Pm := Fintype.piFinset (fun _ : Fin m => A) with hPm
  have hPmc : (Pm.card : ℝ) = (A.card : ℝ) ^ m := by
    rw [hPm, Fintype.card_piFinset]; simp
  set Good := Pm.filter (fun a => F a ≤ 2 * E) with hGood
  have hsumF : ∑ a ∈ Pm, F a ≤ (A.card : ℝ) ^ m * E := sum_sum_samp_sub_pow_le hA hf hr hm1
  -- Markov
  have hGoodc : (A.card : ℝ) ^ m / 2 ≤ Good.card := by
    have hsplit := sum_filter_add_sum_filter_not Pm (fun a => F a ≤ 2 * E) F
    have hc := card_filter_add_card_filter_not (s := Pm) (fun a => F a ≤ 2 * E)
    have hc' : (Good.card : ℝ) + (Pm.filter (fun a => ¬ F a ≤ 2 * E)).card = (A.card : ℝ) ^ m := by
      rw [← hPmc]; exact_mod_cast hc
    have hbad : (2 * E) * (Pm.filter (fun a => ¬ F a ≤ 2 * E)).card ≤
        ∑ a ∈ Pm.filter (fun a => ¬ F a ≤ 2 * E), F a := by
      rw [mul_comm, ← nsmul_eq_mul]
      exact card_nsmul_le_sum _ _ _ (fun a ha => (not_le.1 (mem_filter.1 ha).2).le)
    have hgood0 : 0 ≤ ∑ a ∈ Good, F a := sum_nonneg fun a _ => hFnn a
    rcases hE0.eq_or_lt with hE | hE
    · -- E = 0: no bad samples
      have hbad0 : (Pm.filter (fun a => ¬ F a ≤ 2 * E)) = ∅ := by
        rw [filter_eq_empty_iff]
        intro a ha
        push_neg
        have : ∑ a ∈ Pm, F a ≤ 0 := by rw [← hE] at hsumF; simpa using hsumF
        have := (sum_eq_zero_iff_of_nonneg (fun a _ => hFnn a)).1
          (le_antisymm this (sum_nonneg fun a _ => hFnn a)) a ha
        rw [this, ← hE]; simp
      rw [hbad0, card_empty, Nat.cast_zero, add_zero] at hc'
      rw [hc']; have : (0:ℝ) ≤ (A.card : ℝ) ^ m := by positivity
      linarith
    · have : (2 * E) * (Pm.filter (fun a => ¬ F a ≤ 2 * E)).card ≤ (A.card : ℝ) ^ m * E := by
        linarith
      nlinarith
  -- Pigeonhole
  have hK0 : 0 < K := by
    have h1 : (A.card : ℝ) ≤ (A + Y).card := by
      obtain ⟨y, hy⟩ := hY
      exact_mod_cast card_le_card_of_injOn (· + y) (fun a ha => add_mem_add ha hy)
        (fun a _ b _ h => by simpa using h)
    nlinarith
  set P := Good ×ˢ Y with hP
  set W := Fintype.piFinset (fun _ : Fin m => A + Y) with hW
  have hmaps : ∀ p ∈ P, p.1 + (fun _ => p.2) ∈ W := by
    intro p hp
    rw [mem_product] at hp
    rw [hW, Fintype.mem_piFinset]
    intro i
    have h1 := (mem_filter.1 hp.1).1
    rw [hPm, Fintype.mem_piFinset] at h1
    exact add_mem_add (h1 i) hp.2
  have hWne : W.Nonempty := by
    obtain ⟨a, ha⟩ := hA; obtain ⟨y, hy⟩ := hY
    exact ⟨fun _ => a + y, by rw [hW, Fintype.mem_piFinset]; exact fun _ => add_mem_add ha hy⟩
  have hWc : (W.card : ℝ) ≤ (K * A.card) ^ m := by
    rw [hW, Fintype.card_piFinset]; simp only [prod_const, card_univ, Fintype.card_fin]
    push_cast
    exact pow_le_pow_left₀ (by positivity) hK m
  set b : ℝ := (Y.card : ℝ) / (2 * K ^ m) with hb
  have hnsmul : W.card • b ≤ (P.card : ℝ) := by
    rw [nsmul_eq_mul, hP, card_product, Nat.cast_mul]
    calc (W.card : ℝ) * b ≤ (K * A.card) ^ m * b := by
          gcongr
      _ = (A.card : ℝ) ^ m / 2 * Y.card := by
          rw [hb, mul_pow]; field_simp
      _ ≤ Good.card * Y.card := by gcongr
  obtain ⟨c, -, hc⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hWne hnsmul
  set T := Y.filter (fun t => c - (fun _ => t) ∈ Good) with hT
  have hfib : (P.filter (fun p => p.1 + (fun _ => p.2) = c)).card ≤ T.card := by
    refine card_le_card_of_injOn (fun p => p.2) ?_ ?_
    · intro p hp
      have hp := mem_filter.1 (Finset.mem_coe.1 hp)
      rw [mem_product] at hp
      rw [hT, coe_filter]
      refine ⟨hp.1.2, ?_⟩
      rw [← hp.2]; simpa using hp.1.1
    · intro p hp q hq hpq
      rw [coe_filter, Set.mem_setOf_eq] at hp hq
      simp only at hpq
      have : p.1 = q.1 := by
        have h1 := hp.2; have h2 := hq.2
        rw [hpq] at h1
        rw [← h2] at h1
        exact add_right_cancel h1
      exact Prod.ext this hpq
  refine ⟨T, filter_subset _ _, hc.trans (by exact_mod_cast hfib), ?_⟩
  -- Almost periodicity
  intro t₁ ht₁ t₂ ht₂
  have hg₁ := (mem_filter.1 ht₁).2
  have hg₂ := (mem_filter.1 ht₂).2
  have hF₁ : F (c - fun _ => t₁) ≤ 2 * E := (mem_filter.1 hg₁).2
  have hF₂ : F (c - fun _ => t₂) ≤ 2 * E := (mem_filter.1 hg₂).2
  set s := t₁ - t₂
  have hkey : ∀ x, samp f (c - fun _ => t₂) (x + s) = samp f (c - fun _ => t₁) x := by
    intro x; rw [samp_sub_const, samp_sub_const]; congr 1; simp only [s]; abel
  have hsplit : ∀ x, ψ (x + s) - ψ x = (ψ (x + s) - samp f (c - fun _ => t₂) (x + s)) +
      (samp f (c - fun _ => t₁) x - ψ x) := by
    intro x; rw [hkey]; ring
  have hu : ∑ x, (ψ (x + s) - samp f (c - fun _ => t₂) (x + s)) ^ (2 * r) ≤ 2 * E := by
    rw [sum_add_right (fun x => (ψ x - samp f (c - fun _ => t₂) x) ^ (2 * r)) s]
    calc ∑ x, (ψ x - samp f (c - fun _ => t₂) x) ^ (2 * r) = F (c - fun _ => t₂) := by
          refine sum_congr rfl fun x _ => ?_
          rw [← neg_sub, Even.neg_pow (even_two_mul r)]
      _ ≤ 2 * E := hF₂
  calc ∑ x, (ψ (x + s) - ψ x) ^ (2 * r)
      ≤ ∑ x, 2 ^ (2 * r - 1) * ((ψ (x + s) - samp f (c - fun _ => t₂) (x + s)) ^ (2 * r) +
          (samp f (c - fun _ => t₁) x - ψ x) ^ (2 * r)) := by
        refine sum_le_sum fun x _ => ?_
        rw [hsplit]; exact Even.add_pow_le (even_two_mul r)
    _ = 2 ^ (2 * r - 1) * (∑ x, (ψ (x + s) - samp f (c - fun _ => t₂) (x + s)) ^ (2 * r) +
          F (c - fun _ => t₁)) := by rw [← mul_sum, sum_add_distrib]
    _ ≤ 2 ^ (2 * r - 1) * (2 * E + 2 * E) := by gcongr
    _ = 2 * (16 * (r : ℝ) ^ 2 / m) ^ r * ∑ x, f x ^ (2 * r) := by
        have h1 : (2:ℝ) ^ (2 * r - 1) * 4 = 2 * 4 ^ r := by
          have : (2:ℝ) ^ (2 * r) = 2 ^ (2 * r - 1) * 2 := by rw [← pow_succ]; congr 1; omega
          have h4 : (4:ℝ) ^ r = 2 ^ (2 * r) := by rw [pow_mul]; norm_num
          rw [h4, this]; ring
        have h2 : (16 * (r:ℝ) ^ 2 / m) ^ r = 4 ^ r * (4 * (r:ℝ) ^ 2 / m) ^ r := by
          rw [← mul_pow]; ring_nf
        rw [h2]
        calc (2:ℝ) ^ (2 * r - 1) * (2 * E + 2 * E) = ((2:ℝ) ^ (2 * r - 1) * 4) * E := by ring
          _ = _ := by rw [h1, hE]; ring
    _ ≤ ε ^ (2 * r) * ∑ x, f x ^ (2 * r) := by
        have hsum := sum_nonneg fun x (_ : x ∈ univ) => hF0 x
        gcongr
        have h16 : 16 * (r : ℝ) ^ 2 / m ≤ ε ^ 2 / 2 := by
          rw [div_le_iff₀ hm0]
          have := mul_le_mul_of_nonneg_left hmge (by positivity : (0:ℝ) ≤ ε ^ 2 / 2)
          have e : ε ^ 2 / 2 * (32 * (r : ℝ) ^ 2 / ε ^ 2) = 16 * r ^ 2 := by
            field_simp; ring
          linarith
        calc 2 * (16 * (r : ℝ) ^ 2 / m) ^ r ≤ 2 * (ε ^ 2 / 2) ^ r := by gcongr
          _ = ε ^ (2 * r) * (2 / 2 ^ r) := by rw [div_pow, pow_mul]; ring
          _ ≤ ε ^ (2 * r) * 1 := by
              gcongr
              rw [div_le_one (by positivity)]
              calc (2:ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
          _ = ε ^ (2 * r) := mul_one _

end

end KM

end KMFile_CrootSisask

section KMFile_LinfAP



/-!
# `L^∞` almost periodicity for `⟨μ_{A₁} ○ μ_{A₂}, 1_S⟩` along iterated sumsets
-/

open Finset
open scoped Pointwise

namespace KM

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Telescoping along iterated convolutions. -/
lemma iconv_telescope {X : Finset G} (hX : X.Nonempty) (Φ : G → ℝ) {δ : ℝ}
    (h : ∀ y, ∀ x ∈ X, |Φ (y + x) - Φ y| ≤ δ) (k : ℕ) :
    |∑ y, iconv (mu X) k y * Φ y - Φ 0| ≤ k * δ := by
  induction k with
  | zero =>
    simp only [iconv, ind_apply, mem_singleton, ite_mul, one_mul, zero_mul, sum_ite_eq',
      mem_univ, if_true, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ k ih =>
    have hI := sum_iconv (sum_mu hX) k
    have hInn := iconv_nonneg (mu_nonneg' X) k
    have e : ∑ y, iconv (mu X) (k + 1) y * Φ y =
        ∑ x, mu X x * ∑ y, iconv (mu X) k y * Φ (y + x) := by
      rw [iconv, sum_conv_mul]
    have hstep : |∑ x, mu X x * ∑ y, iconv (mu X) k y * Φ (y + x) -
        ∑ y, iconv (mu X) k y * Φ y| ≤ δ := by
      have e2 : ∑ x, mu X x * ∑ y, iconv (mu X) k y * Φ (y + x) - ∑ y, iconv (mu X) k y * Φ y =
          ∑ x, mu X x * ∑ y, iconv (mu X) k y * (Φ (y + x) - Φ y) := by
        have : ∑ y, iconv (mu X) k y * Φ y = ∑ x, mu X x * ∑ y, iconv (mu X) k y * Φ y := by
          rw [← sum_mul, sum_mu hX, one_mul]
        rw [this, ← sum_sub_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [← mul_sub, ← sum_sub_distrib]
        simp_rw [mul_sub]
      rw [e2]
      calc |∑ x, mu X x * ∑ y, iconv (mu X) k y * (Φ (y + x) - Φ y)|
          ≤ ∑ x, |mu X x * ∑ y, iconv (mu X) k y * (Φ (y + x) - Φ y)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ x, mu X x * δ := by
            refine sum_le_sum fun x _ => ?_
            rw [abs_mul, abs_of_nonneg (mu_nonneg X x)]
            by_cases hx : x ∈ X
            · gcongr
              · exact mu_nonneg X x
              calc |∑ y, iconv (mu X) k y * (Φ (y + x) - Φ y)|
                  ≤ ∑ y, |iconv (mu X) k y * (Φ (y + x) - Φ y)| := abs_sum_le_sum_abs _ _
                _ ≤ ∑ y, iconv (mu X) k y * δ := by
                    refine sum_le_sum fun y _ => ?_
                    rw [abs_mul, abs_of_nonneg (hInn y)]
                    exact mul_le_mul_of_nonneg_left (h y x hx) (hInn y)
                _ = δ := by rw [← sum_mul, hI, one_mul]
            · simp [mu_apply, hx]
        _ = δ := by rw [← sum_mul, sum_mu hX, one_mul]
    rw [e]
    calc |∑ x, mu X x * ∑ y, iconv (mu X) k y * Φ (y + x) - Φ 0|
        ≤ |∑ x, mu X x * ∑ y, iconv (mu X) k y * Φ (y + x) - ∑ y, iconv (mu X) k y * Φ y| +
          |∑ y, iconv (mu X) k y * Φ y - Φ 0| := abs_sub_le _ _ _
      _ ≤ δ + k * δ := add_le_add hstep ih
      _ = ((k + 1 : ℕ) : ℝ) * δ := by push_cast; ring

/-- The correlation function `Φ(y) = ⟨μ_{A₁} ○ μ_{A₂}, τ_{-y} 1_S⟩`. -/
def corrF (A₁ A₂ S : Finset G) (y : G) : ℝ := ∑ x, dconv (mu A₁) (mu A₂) x * ind S (x + y)

lemma corrF_eq (A₁ A₂ S : Finset G) (y : G) :
    corrF A₁ A₂ S y = ∑ w, mu A₁ w * conv (mu A₂) (ind S) (w + y) := by
  unfold corrF dconv conv
  simp_rw [sum_mul]
  rw [sum_comm]
  calc ∑ z, ∑ x, mu A₁ (x + z) * mu A₂ z * ind S (x + y)
      = ∑ z, ∑ w, mu A₁ w * mu A₂ z * ind S (w + y - z) := by
        refine sum_congr rfl fun z _ => ?_
        exact Fintype.sum_equiv (Equiv.addRight z) _ _ (fun x => by
          simp only [Equiv.coe_addRight]; rw [show x + z + y - z = x + y by abel])
    _ = _ := by
        rw [sum_comm]
        refine sum_congr rfl fun w _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun z _ => ?_
        ring

lemma sum_conv_iconv_mul_ind (X A₁ A₂ S : Finset G) (k : ℕ) :
    ∑ x, conv (iconv (mu X) k) (dconv (mu A₁) (mu A₂)) x * ind S x =
      ∑ y, iconv (mu X) k y * corrF A₁ A₂ S y := by
  rw [sum_conv_mul]; rfl

/-- **`L^∞` almost periodicity** (Schoen–Sisask Theorem 5.1, crude form). -/
theorem linf_almost_periodic {A₁ A₂ S Y : Finset G} (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hY : Y.Nonempty) {K : ℝ} (hK : ((A₂ + Y).card : ℝ) ≤ K * A₂.card) {r : ℕ} (hr : 1 ≤ r)
    (hS : (S.card : ℝ) ≤ 4 ^ r * A₁.card) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ T ⊆ Y, (Y.card : ℝ) / (2 * K ^ csM r (ε / (2 * k))) ≤ T.card ∧
      ∀ z ∈ T, T.Nonempty ∧ |∑ x, conv (iconv (mu (T.image (· - z))) k)
        (dconv (mu A₁) (mu A₂)) x * ind S x - ∑ x, dconv (mu A₁) (mu A₂) x * ind S x| ≤ ε := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set ε' := ε / (2 * k) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨T, hTY, hTc, hT⟩ := croot_sisask hA₂ hY hK (fun x => ind_nonneg S x) hr hε'0
  refine ⟨T, hTY, hTc, fun z hz => ⟨⟨z, hz⟩, ?_⟩⟩
  set ψ := conv (mu A₂) (ind S) with hψ
  have hA₁c : (0 : ℝ) < A₁.card := by exact_mod_cast hA₁.card_pos
  have hind : ∑ x, ind S x ^ (2 * r) = S.card := by
    rw [← sum_ind S]; refine sum_congr rfl fun x _ => ?_
    unfold ind; split_ifs <;> simp; omega
  -- pointwise almost invariance of `corrF`
  have hinv : ∀ y, ∀ x ∈ T.image (· - z), |corrF A₁ A₂ S (y + x) - corrF A₁ A₂ S y| ≤ ε / k := by
    intro y x hx
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hx
    set d := corrF A₁ A₂ S (y + (t - z)) - corrF A₁ A₂ S y with hd
    have hd' : d = ∑ w, mu A₁ w * (ψ (w + y + (t - z)) - ψ (w + y)) := by
      rw [hd, corrF_eq, corrF_eq, ← sum_sub_distrib]
      refine sum_congr rfl fun w _ => ?_
      rw [mul_sub, add_assoc]
    have h1 : |d| ^ (2 * r) ≤ ∑ w, mu A₁ w * (ψ (w + y + (t - z)) - ψ (w + y)) ^ (2 * r) := by
      have habs : |d| ≤ ∑ w, mu A₁ w * |ψ (w + y + (t - z)) - ψ (w + y)| := by
        rw [hd']
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine sum_congr rfl fun w _ => ?_
        rw [abs_mul, abs_of_nonneg (mu_nonneg A₁ w)]
      have hJ := Real.pow_arith_mean_le_arith_mean_pow univ (mu A₁)
        (fun w => |ψ (w + y + (t - z)) - ψ (w + y)|) (fun w _ => mu_nonneg A₁ w) (sum_mu hA₁)
        (fun w _ => abs_nonneg _) (2 * r)
      calc |d| ^ (2 * r) ≤ (∑ w, mu A₁ w * |ψ (w + y + (t - z)) - ψ (w + y)|) ^ (2 * r) :=
            pow_le_pow_left₀ (abs_nonneg _) habs _
        _ ≤ _ := hJ
        _ = _ := by
            refine sum_congr rfl fun w _ => ?_
            rw [(even_two_mul r).pow_abs]
    have h2 : ∑ w, mu A₁ w * (ψ (w + y + (t - z)) - ψ (w + y)) ^ (2 * r) ≤
        (A₁.card : ℝ)⁻¹ * ∑ u, (ψ (u + (t - z)) - ψ u) ^ (2 * r) := by
      calc ∑ w, mu A₁ w * (ψ (w + y + (t - z)) - ψ (w + y)) ^ (2 * r)
          ≤ ∑ w, (A₁.card : ℝ)⁻¹ * (ψ (w + y + (t - z)) - ψ (w + y)) ^ (2 * r) :=
            sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (mu_le A₁ w)
              ((even_two_mul r).pow_nonneg _)
        _ = (A₁.card : ℝ)⁻¹ * ∑ u, (ψ (u + (t - z)) - ψ u) ^ (2 * r) := by
            rw [← mul_sum]
            congr 1
            exact sum_add_right (fun u => (ψ (u + (t - z)) - ψ u) ^ (2 * r)) y
    have h3 := hT t ht z hz
    rw [hind] at h3
    have h4 : |d| ^ (2 * r) ≤ (ε / k) ^ (2 * r) := by
      calc |d| ^ (2 * r) ≤ (A₁.card : ℝ)⁻¹ * (ε' ^ (2 * r) * S.card) := by
            refine h1.trans (h2.trans ?_)
            gcongr
        _ ≤ (A₁.card : ℝ)⁻¹ * (ε' ^ (2 * r) * (4 ^ r * A₁.card)) := by gcongr
        _ = (ε / k) ^ (2 * r) := by
            rw [hε', show (4:ℝ) ^ r = 2 ^ (2 * r) by rw [pow_mul]; norm_num]
            rw [div_pow, div_pow, mul_pow]; field_simp
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by omega)).1 h4
  have hXne : (T.image (· - z)).Nonempty := ⟨0, mem_image.2 ⟨z, hz, sub_self z⟩⟩
  have htel := iconv_telescope hXne (corrF A₁ A₂ S) hinv k
  rw [sum_conv_iconv_mul_ind]
  have h0 : ∑ x, dconv (mu A₁) (mu A₂) x * ind S x = corrF A₁ A₂ S 0 := by
    unfold corrF; simp
  rw [h0]
  calc _ ≤ (k : ℝ) * (ε / k) := htel
    _ = ε := by field_simp

end

end KM

end KMFile_LinfAP

section KMFile_Fourier



/-!
# Fourier analysis on `ZMod N`
-/

open Finset
open ComplexConjugate

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The character `x ↦ e(x/N)`. -/
def ech (z : ZMod N) : ℂ := ZMod.stdAddChar z

lemma ech_add (a b : ZMod N) : ech (a + b) = ech a * ech b := AddChar.map_add_eq_mul _ _ _

@[simp] lemma ech_zero : ech (0 : ZMod N) = 1 := AddChar.map_zero_eq_one _

lemma ech_neg (a : ZMod N) : ech (-a) = conj (ech a) := AddChar.map_neg_eq_conj _ _

@[simp] lemma norm_ech (a : ZMod N) : ‖ech a‖ = 1 := AddChar.norm_apply _ _

lemma ech_sub (a b : ZMod N) : ech (a - b) = ech a * ech (-b) := by
  rw [sub_eq_add_neg, ech_add]

lemma ech_mul_ech_neg (a : ZMod N) : ech a * ech (-a) = 1 := by
  rw [← ech_add, add_neg_cancel, ech_zero]

lemma sum_ech_mul (γ : ZMod N) : ∑ x, ech (x * γ) = if γ = 0 then (N : ℂ) else 0 := by
  have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod N) ℂ)) γ
    (ZMod.isPrimitive_stdAddChar N)
  unfold ech; rw [this]; split_ifs <;> simp [ZMod.card]

/-- Fourier transform. -/
def ft (f : ZMod N → ℝ) (γ : ZMod N) : ℂ := ∑ x, (f x : ℂ) * ech (-(γ * x))

lemma norm_ft_le (f : ZMod N → ℝ) (γ : ZMod N) : ‖ft f γ‖ ≤ ∑ x, |f x| := by
  unfold ft
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine sum_congr rfl fun x _ => ?_
  rw [norm_mul, norm_ech, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma ft_mu_zero {S : Finset (ZMod N)} (hS : S.Nonempty) : ft (mu S) 0 = 1 := by
  unfold ft
  simp only [zero_mul, neg_zero, ech_zero, mul_one]
  rw [← Complex.ofReal_sum, sum_mu hS, Complex.ofReal_one]

lemma norm_ft_mu_le (S : Finset (ZMod N)) (hS : S.Nonempty) (γ : ZMod N) : ‖ft (mu S) γ‖ ≤ 1 := by
  refine (norm_ft_le _ γ).trans (le_of_eq ?_)
  rw [← sum_mu hS]; refine sum_congr rfl fun x _ => abs_of_nonneg (mu_nonneg S x)

/-- Fourier inversion. -/
theorem ft_inv (f : ZMod N → ℝ) (x : ZMod N) :
    ((N : ℂ))⁻¹ * ∑ γ, ft f γ * ech (γ * x) = f x := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold ft
  simp_rw [sum_mul]
  rw [sum_comm]
  have : ∀ y, ∑ γ, (f y : ℂ) * ech (-(γ * y)) * ech (γ * x) =
      (f y : ℂ) * if x - y = 0 then (N : ℂ) else 0 := by
    intro y
    rw [← sum_ech_mul, mul_sum]
    refine sum_congr rfl fun γ _ => ?_
    rw [mul_assoc, ← ech_add]; congr 2; ring
  simp_rw [this]
  simp only [sub_eq_zero, mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_univ, if_true]
  field_simp

lemma ft_conv (f g : ZMod N → ℝ) (γ : ZMod N) : ft (conv f g) γ = ft f γ * ft g γ := by
  unfold ft conv
  rw [sum_mul_sum]
  simp_rw [Complex.ofReal_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← Fintype.sum_equiv (Equiv.addRight y) _ _ (fun x => rfl)]
  refine sum_congr rfl fun x _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, Complex.ofReal_mul]
  rw [show -(γ * (x + y)) = -(γ * y) + -(γ * x) by ring, ech_add]
  ring

lemma ft_neg (g : ZMod N → ℝ) (γ : ZMod N) : ft (fun x => g (-x)) γ = conj (ft g γ) := by
  unfold ft
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun x => ?_)
  simp only [Equiv.neg_apply, map_mul, Complex.conj_ofReal, neg_neg]
  rw [← ech_neg]; congr 2; ring

lemma ft_dconv (f g : ZMod N → ℝ) (γ : ZMod N) : ft (dconv f g) γ = ft f γ * conj (ft g γ) := by
  rw [dconv_eq_conv_neg, ft_conv, ft_neg]

lemma ft_translate (f : ZMod N → ℝ) (t γ : ZMod N) :
    ft (fun x => f (x - t)) γ = ech (-(γ * t)) * ft f γ := by
  unfold ft
  rw [mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight t) _ _ (fun x => ?_)
  simp only [Equiv.subRight_apply]
  rw [show -(γ * x) = -(γ * t) + -(γ * (x - t)) by ring, ech_add]; ring

/-- Parseval. -/
theorem parseval (f : ZMod N → ℝ) : ∑ γ, ‖ft f γ‖ ^ 2 = N * ∑ x, f x ^ 2 := by
  have h : ∀ γ, ((‖ft f γ‖ ^ 2 : ℝ) : ℂ) = ft f γ * conj (ft f γ) := by
    intro γ; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : (((∑ γ, ‖ft f γ‖ ^ 2 : ℝ)) : ℂ) = ((N * ∑ x, f x ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [h]
    have e1 : ∀ γ, ft f γ * conj (ft f γ) = ∑ x, ∑ y, (f x : ℂ) * f y * ech ((y - x) * γ) := by
      intro γ
      unfold ft
      rw [map_sum, sum_mul_sum]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      rw [map_mul, Complex.conj_ofReal, ← ech_neg, neg_neg]
      rw [show (y - x) * γ = -(γ * x) + γ * y by ring, ech_add]; ring
    simp_rw [e1]
    rw [sum_comm, sum_congr rfl fun x _ => sum_comm]
    have e2 : ∀ x y : ZMod N, ∑ γ, (f x : ℂ) * f y * ech ((y - x) * γ) =
        (f x : ℂ) * f y * if y - x = 0 then (N : ℂ) else 0 := by
      intro x y
      rw [← mul_sum]; congr 1
      rw [← sum_ech_mul]; refine sum_congr rfl fun γ _ => ?_; rw [mul_comm]
    simp_rw [e2]
    simp only [sub_eq_zero, mul_ite, mul_zero]
    simp_rw [sum_ite_eq']
    simp only [mem_univ, if_true]
    push_cast
    rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; ring
  exact_mod_cast key

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

/-- Difference of translates via Fourier inversion. -/
lemma abs_sub_translate_le (f : ZMod N → ℝ) (x t : ZMod N) :
    |f (x + t) - f x| ≤ (N : ℝ)⁻¹ * ∑ γ, ‖ft f γ‖ * ‖ech (γ * t) - 1‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have e : ((f (x + t) - f x : ℝ) : ℂ) =
      ((N : ℂ))⁻¹ * ∑ γ, ft f γ * ech (γ * x) * (ech (γ * t) - 1) := by
    push_cast
    rw [← ft_inv f (x + t), ← ft_inv f x, ← mul_sub, ← sum_sub_distrib]
    congr 1; refine sum_congr rfl fun γ _ => ?_
    rw [mul_add, ech_add]; ring
  have : |f (x + t) - f x| = ‖((f (x + t) - f x : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [this, e, norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine sum_congr rfl fun γ _ => ?_
  rw [norm_mul, norm_mul, norm_ech, mul_one]

end

end KM

end KMFile_Fourier

section KMFile_ChangCore



/-!
# Chang's lemma via exponential moments and Riesz products
-/

open Finset
open ComplexConjugate

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma ech_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod N) :
    ech (∑ i ∈ s, f i) = ∏ i ∈ s, ech (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, ech_add, ih]

/-- Coefficients `0, 1, -1`. -/
def cf : Fin 3 → ℤ := ![0, 1, -1]

/-- The signed combination of the elements of `Δ` with coefficients `ε`. -/
def comb (Δ : Finset (ZMod N)) (ε : Δ → Fin 3) : ZMod N := ∑ l : Δ, (cf (ε l) : ZMod N) * l

lemma comb_zero (Δ : Finset (ZMod N)) : comb Δ (fun _ => 0) = 0 := by
  simp [comb, cf]

/-- The Riesz product coefficient. -/
def rc (s : ℝ) (c : ℂ) : Fin 3 → ℂ := ![1, (s / 2 : ℂ) * c, (s / 2 : ℂ) * conj c]

lemma norm_rc_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {c : ℂ} (hc : ‖c‖ ≤ 1) (j : Fin 3) :
    ‖rc s c j‖ ≤ 1 := by
  fin_cases j <;> simp [rc]
  all_goals rw [abs_of_nonneg hs0]; nlinarith [norm_nonneg c]

lemma one_add_re_eq (s : ℝ) (c : ℂ) (l x : ZMod N) :
    ((1 + s * (c * ech (-(l * x))).re : ℝ) : ℂ) =
      ∑ j : Fin 3, rc s c j * ech (-((cf j : ZMod N) * l * x)) := by
  rw [Fin.sum_univ_three]
  simp only [rc, cf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Int.cast_zero, zero_mul, neg_zero, ech_zero, mul_one, Int.cast_one, one_mul,
    neg_mul, neg_neg]
  have h1 : ((c * ech (-(l * x))).re : ℂ) = (c * ech (-(l * x)) + conj (c * ech (-(l * x)))) / 2 := by
    rw [Complex.add_conj]; push_cast; ring
  have h2 : conj (c * ech (-(l * x))) = conj c * ech (l * x) := by
    rw [map_mul, ← ech_neg, neg_neg]
  push_cast
  rw [h1, h2]
  simp only [Matrix.cons_val, Matrix.tail_cons, Matrix.head_cons]
  push_cast
  rw [show -(-1 * l * x) = l * x by ring]
  ring

/-- **Riesz product bound.** -/
theorem riesz_bound (Δ : Finset (ZMod N)) (c : ZMod N → ℂ) (hc : ∀ l, ‖c l‖ ≤ 1) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {β : ZMod N → ℝ} (hβ1 : ∑ x, β x = 1) {η : ℝ}
    (hη : ∀ ε : Δ → Fin 3, ε ≠ (fun _ => 0) → ‖ft β (comb Δ ε)‖ ≤ η) (hη0 : 0 ≤ η) :
    ∑ x, β x * ∏ l ∈ Δ, (1 + s * (c l * ech (-(l * x))).re) ≤ 1 + 3 ^ Δ.card * η := by
  set a : Δ → Fin 3 → ℂ := fun l j => rc s (c l) j
  have hexp : ∀ x, ((∏ l ∈ Δ, (1 + s * (c l * ech (-(l * x))).re) : ℝ) : ℂ) =
      ∑ ε : Δ → Fin 3, (∏ l, a l (ε l)) * ech (-(comb Δ ε * x)) := by
    intro x
    push_cast
    rw [← prod_coe_sort Δ]
    have : ∀ l : Δ, (1 + (s : ℂ) * ((c l * ech (-((l : ZMod N) * x))).re : ℂ)) =
        ∑ j : Fin 3, a l j * ech (-((cf j : ZMod N) * (l : ZMod N) * x)) := by
      intro l; rw [← one_add_re_eq]; push_cast; ring
    simp_rw [this]
    rw [Fintype.prod_sum]
    refine sum_congr rfl fun ε _ => ?_
    rw [prod_mul_distrib, ← ech_sum]
    congr 2
    unfold comb
    rw [sum_mul, ← sum_neg_distrib]
  have hsum : ((∑ x, β x * ∏ l ∈ Δ, (1 + s * (c l * ech (-(l * x))).re) : ℝ) : ℂ) =
      ∑ ε : Δ → Fin 3, (∏ l, a l (ε l)) * ft β (comb Δ ε) := by
    rw [Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
    simp only [hexp]
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun ε _ => ?_
    unfold ft
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    ring
  have hle : ∑ x, β x * ∏ l ∈ Δ, (1 + s * (c l * ech (-(l * x))).re) ≤
      ‖∑ ε : Δ → Fin 3, (∏ l, a l (ε l)) * ft β (comb Δ ε)‖ := by
    rw [← hsum, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  refine hle.trans ((norm_sum_le _ _).trans ?_)
  rw [← add_sum_erase _ _ (mem_univ (fun _ : Δ => (0 : Fin 3)))]
  have h0 : ‖(∏ l, a l ((fun _ : Δ => (0 : Fin 3)) l)) * ft β (comb Δ (fun _ : Δ => 0))‖ = 1 := by
    have ha : ∀ l, a l 0 = 1 := fun l => rfl
    simp only [ha, prod_const_one, one_mul, comb_zero]
    unfold ft
    simp only [zero_mul, neg_zero, ech_zero, mul_one]
    rw [← Complex.ofReal_sum, hβ1]; simp
  have hrest : ∑ ε ∈ univ.erase (fun _ : Δ => (0 : Fin 3)), ‖(∏ l, a l (ε l)) * ft β (comb Δ ε)‖ ≤
      3 ^ Δ.card * η := by
    calc ∑ ε ∈ univ.erase (fun _ : Δ => (0 : Fin 3)), ‖(∏ l, a l (ε l)) * ft β (comb Δ ε)‖
        ≤ ∑ ε ∈ univ.erase (fun _ : Δ => (0 : Fin 3)), η := by
          refine sum_le_sum fun ε hε => ?_
          rw [norm_mul]
          have h1 := hη ε (ne_of_mem_erase hε)
          have hp : ‖∏ l, a l (ε l)‖ ≤ 1 := by
            rw [norm_prod]
            exact prod_le_one (fun _ _ => norm_nonneg _) (fun l _ => norm_rc_le hs0 hs1 (hc l) _)
          calc ‖∏ l, a l (ε l)‖ * ‖ft β (comb Δ ε)‖ ≤ 1 * η := by
                gcongr
            _ = η := one_mul η
      _ = ((univ.erase (fun _ : Δ => (0 : Fin 3))).card : ℝ) * η := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 ^ Δ.card * η := by
          gcongr
          have : (univ.erase (fun _ : Δ => (0 : Fin 3)) : Finset (Δ → Fin 3)).card ≤ 3 ^ Δ.card := by
            refine (card_erase_le).trans (le_of_eq ?_)
            simp [Fintype.card_fun]
          exact_mod_cast this
  rw [h0]; linarith

lemma exp_mul_le_cosh_add {y : ℝ} (hy : |y| ≤ 1) (t : ℝ) :
    Real.exp (t * y) ≤ Real.cosh t + y * Real.sinh t := by
  have hy1 := (abs_le.1 hy)
  set a := (1 + y) / 2
  set b := (1 - y) / 2
  have ha : 0 ≤ a := by simp only [a]; linarith
  have hb : 0 ≤ b := by simp only [b]; linarith
  have hab : a + b = 1 := by simp only [a, b]; ring
  have h := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ (-t)) ha hb hab
  simp only [smul_eq_mul] at h
  have e : a * t + b * -t = t * y := by simp only [a, b]; ring
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  rw [Real.cosh_eq, Real.sinh_eq]; simp only [a, b]; ring

/-- **Chang's bound** (exponential-moment form): a set `Δ` of large Fourier coefficients of `μ_X`
which is "dissociated relative to `β`" has size `O(log C)`. -/
theorem chang_bound {X : Finset (ZMod N)} (hX : X.Nonempty) {β : ZMod N → ℝ}
    (hβ : ∀ x, 0 ≤ β x) (hβ1 : ∑ x, β x = 1) {C : ℝ} (hC : ∀ x, mu X x ≤ C * β x)
    (Δ : Finset (ZMod N)) (hΔ : ∀ l ∈ Δ, 1 / 2 ≤ ‖ft (mu X) l‖) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ ε : Δ → Fin 3, ε ≠ (fun _ => 0) → ‖ft β (comb Δ ε)‖ ≤ η)
    (h3 : 3 ^ Δ.card * η ≤ 1) :
    Real.exp (Δ.card / 8) ≤ 2 * C := by
  set u : ZMod N → ℂ := fun l => ft (mu X) l
  set c : ZMod N → ℂ := fun l => conj (u l) / (‖u l‖ : ℂ)
  have hc : ∀ l, ‖c l‖ ≤ 1 := by
    intro l
    simp only [c, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
    by_cases h : ‖u l‖ = 0
    · rw [h]; simp
    · rw [div_self h]
  set y : ZMod N → ZMod N → ℝ := fun l x => (c l * ech (-(l * x))).re
  have hy : ∀ l x, |y l x| ≤ 1 := by
    intro l x
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_ech, mul_one]; exact hc l
  have hcorr : ∀ l ∈ Δ, ∑ x, mu X x * y l x = ‖u l‖ := by
    intro l hl
    have hu0 : ‖u l‖ ≠ 0 := by have := hΔ l hl; simp only [u] at *; linarith
    have e : ∑ x, mu X x * y l x = (c l * u l).re := by
      simp only [y, u, ft]
      rw [mul_sum, Complex.re_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← Complex.re_ofReal_mul]; congr 1; ring
    rw [e]
    simp only [c]
    rw [div_mul_eq_mul_div, Complex.conj_mul', ← Complex.ofReal_pow]
    rw [show ((‖u l‖ ^ 2 : ℝ) : ℂ) / (‖u l‖ : ℂ) = ((‖u l‖ ^ 2 / ‖u l‖ : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.ofReal_re]; field_simp
  set f : ZMod N → ℝ := fun x => ∑ l ∈ Δ, y l x
  have hmean : (Δ.card : ℝ) / 2 ≤ ∑ x, mu X x * f x := by
    simp only [f, mul_sum]
    rw [sum_comm]
    calc (Δ.card : ℝ) / 2 = ∑ l ∈ Δ, (1 / 2 : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ l ∈ Δ, ∑ x, mu X x * y l x := by
          refine sum_le_sum fun l hl => ?_
          rw [hcorr l hl]; exact hΔ l hl
  -- Jensen
  have hJ : Real.exp ((1 / 2) * ∑ x, mu X x * f x) ≤ ∑ x, mu X x * Real.exp (f x / 2) := by
    have := convexOn_exp.map_sum_le (t := univ) (w := mu X) (p := fun x => f x / 2)
      (fun x _ => mu_nonneg X x) (sum_mu hX) (fun x _ => Set.mem_univ _)
    simp only [smul_eq_mul] at this
    refine le_trans (le_of_eq ?_) this
    congr 1; rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; ring
  set s := Real.sinh (1 / 2) / Real.cosh (1 / 2)
  have hcosh : 0 < Real.cosh (1 / 2) := Real.cosh_pos _
  have hs0 : 0 ≤ s := div_nonneg (Real.sinh_nonneg_iff.2 (by norm_num)) hcosh.le
  have hs1 : s ≤ 1 := (div_le_one hcosh).2 (Real.sinh_lt_cosh _).le
  have hptexp : ∀ x, Real.exp (f x / 2) ≤
      Real.cosh (1 / 2) ^ Δ.card * ∏ l ∈ Δ, (1 + s * y l x) := by
    intro x
    have : Real.exp (f x / 2) = ∏ l ∈ Δ, Real.exp ((1 / 2) * y l x) := by
      rw [← Real.exp_sum]; congr 1; simp only [f]; rw [sum_div]
      refine sum_congr rfl fun l _ => ?_; ring
    rw [this, ← prod_const, ← prod_mul_distrib]
    refine prod_le_prod (fun l _ => (Real.exp_pos _).le) (fun l _ => ?_)
    refine (exp_mul_le_cosh_add (hy l x) _).trans (le_of_eq ?_)
    simp only [s]; field_simp
  have hR := riesz_bound Δ c hc hs0 hs1 hβ1 hη hη0
  have hC0 : 0 ≤ C := by
    obtain ⟨x0, hx0⟩ := id hX
    have h1 := hC x0
    have h2 : 0 < mu X x0 := by simp [mu_apply, hx0, hX.card_pos]
    by_contra hneg; push_neg at hneg
    nlinarith [hβ x0]
  have hmain : ∑ x, mu X x * Real.exp (f x / 2) ≤ 2 * C * Real.exp (Δ.card / 8) := by
    calc ∑ x, mu X x * Real.exp (f x / 2) ≤ ∑ x, C * β x * Real.exp (f x / 2) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le
      _ ≤ ∑ x, C * β x * (Real.cosh (1 / 2) ^ Δ.card * ∏ l ∈ Δ, (1 + s * y l x)) := by
          refine sum_le_sum fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (hptexp x) (mul_nonneg hC0 (hβ x))
      _ = C * Real.cosh (1 / 2) ^ Δ.card * ∑ x, β x * ∏ l ∈ Δ, (1 + s * y l x) := by
          rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; ring
      _ ≤ C * Real.cosh (1 / 2) ^ Δ.card * (1 + 3 ^ Δ.card * η) := by
          gcongr
      _ ≤ C * Real.exp (1 / 8) ^ Δ.card * 2 := by
          gcongr
          · have := Real.cosh_le_exp_half_sq (1 / 2)
            refine this.trans (le_of_eq ?_); norm_num
          · linarith
      _ = 2 * C * Real.exp (Δ.card / 8) := by
          rw [← Real.exp_nat_mul]; ring_nf
  have hlow : Real.exp (Δ.card / 4) ≤ Real.exp ((1 / 2) * ∑ x, mu X x * f x) := by
    rw [Real.exp_le_exp]; linarith
  have := hlow.trans (hJ.trans hmain)
  have e : Real.exp ((Δ.card : ℝ) / 4) = Real.exp (Δ.card / 8) * Real.exp (Δ.card / 8) := by
    rw [← Real.exp_add]; ring_nf
  rw [e] at this
  have hpos := Real.exp_pos ((Δ.card : ℝ) / 8)
  nlinarith

end

end KM

end KMFile_ChangCore

section KMFile_LocalChang



/-!
# Local Chang lemma (Sanders' local version, via relative dissociativity)
-/

open Finset
open ComplexConjugate

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma ft_sub (f g : ZMod N → ℝ) (γ : ZMod N) :
    ft (fun x => f x - g x) γ = ft f γ - ft g γ := by
  unfold ft; rw [← sum_sub_distrib]; refine sum_congr rfl fun x _ => ?_; push_cast; ring

lemma ft_ind_zero (γ : ZMod N) : ft (ind {0}) γ = 1 := by
  unfold ft
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp [ind_apply]
  · intro b _ hb; simp [ind_apply, hb]
  · simp

lemma ft_iconv (f : ZMod N → ℝ) (k : ℕ) (γ : ZMod N) : ft (iconv f k) γ = ft f γ ^ k := by
  induction k with
  | zero => simp [iconv, ft_ind_zero]
  | succ k ih => rw [iconv, ft_conv, ih, pow_succ, mul_comm]

lemma norm_ech_add_sub_one_le (a b : ZMod N) :
    ‖ech (a + b) - 1‖ ≤ ‖ech a - 1‖ + ‖ech b - 1‖ := by
  rw [ech_add]
  calc ‖ech a * ech b - 1‖ = ‖ech a * (ech b - 1) + (ech a - 1)‖ := by ring_nf
    _ ≤ ‖ech a * (ech b - 1)‖ + ‖ech a - 1‖ := norm_add_le _ _
    _ = ‖ech a - 1‖ + ‖ech b - 1‖ := by rw [norm_mul, norm_ech, one_mul, add_comm]

lemma norm_ech_neg_sub_one (a : ZMod N) : ‖ech (-a) - 1‖ = ‖ech a - 1‖ := by
  have : ech (-a) - 1 = conj (ech a - 1) := by rw [map_sub, map_one, ech_neg]
  rw [this, Complex.norm_conj]

lemma norm_ech_cf_mul_sub_one_le (j : Fin 3) (a : ZMod N) :
    ‖ech ((cf j : ZMod N) * a) - 1‖ ≤ ‖ech a - 1‖ := by
  fin_cases j <;> simp [cf, norm_ech_neg_sub_one]

lemma norm_ech_sum_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → ZMod N) :
    ‖ech (∑ i ∈ s, f i) - 1‖ ≤ ∑ i ∈ s, ‖ech (f i) - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (norm_ech_add_sub_one_le _ _).trans (add_le_add_right ih _)

/-- `Δ` is dissociated relative to `S`: no non-trivial `{0, ±1}`-combination lies in `S`. -/
def SDissoc (S Δ : Finset (ZMod N)) : Prop :=
  ∀ E : ZMod N → Fin 3, (∃ z ∈ Δ, E z ≠ 0) → ∑ z ∈ Δ, (cf (E z) : ZMod N) * z ∉ S

lemma comb_eq_sum (Δ : Finset (ZMod N)) (ε : Δ → Fin 3) :
    comb Δ ε = ∑ z ∈ Δ, (cf (if h : z ∈ Δ then ε ⟨z, h⟩ else 0) : ZMod N) * z := by
  unfold comb
  rw [← sum_coe_sort Δ]
  refine sum_congr rfl fun z _ => ?_
  simp [z.2]

/-- **Local Chang lemma.** -/
theorem local_chang {Γ : Finset (ZMod N)} {ρ κ ε₁ : ℝ} (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hε₁ : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hreg : IsReg Γ ρ κ ε₁) {T : Finset (ZMod N)}
    (hT : T ⊆ bohr Γ ρ) (hTne : T.Nonempty) {σ : ℝ} (hσ : 0 < σ)
    (hTσ : σ * (bohr Γ ρ).card ≤ T.card) {ρ₀ κ₀ ε₀ : ℝ} (hρ₀ : 0 < ρ₀) (hκ₀ : 0 ≤ κ₀)
    (hε₀ : 0 ≤ ε₀) (hreg₀ : IsReg Γ ρ₀ κ₀ ε₀) {L : ℕ} (hLρ : L * ρ₀ ≤ κ * ρ)
    (hL : 8 * Real.log (4 / σ) < L) :
    ∃ Δ : Finset (ZMod N), Δ.card ≤ L ∧ ∀ γ, 1 / 2 ≤ ‖ft (mu T) γ‖ → ∀ ρ' : ℝ,
      ∀ t ∈ bohr Γ (κ₀ * ρ₀), t ∈ bohr Δ ρ' →
        ‖ech (γ * t) - 1‖ ≤ 6 * ε₀ + Δ.card * (2 * Real.pi * ρ') := by
  classical
  set B₀ := bohr Γ ρ₀ with hB₀
  set ν := iconv (mu B₀) L with hν
  set Yp := bohr Γ (ρ * (1 + κ)) with hYp
  set β := conv ν (mu Yp) with hβ
  have hB₀ne : B₀.Nonempty := bohr_nonempty hρ₀.le
  have hYpne : Yp.Nonempty := bohr_nonempty (by positivity)
  have hνnn : ∀ x, 0 ≤ ν x := iconv_nonneg (mu_nonneg' B₀) L
  have hν1 : ∑ x, ν x = 1 := sum_iconv (sum_mu hB₀ne) L
  have hβnn : ∀ x, 0 ≤ β x := conv_nonneg hνnn (mu_nonneg' Yp)
  have hβ1 : ∑ x, β x = 1 := by rw [hβ, sum_conv, hν1, sum_mu hYpne, one_mul]
  have hνsupp : SuppIn ν Γ (κ * ρ) := (suppIn_iconv_mu hρ₀.le L).mono hLρ
  -- `μ_T ≤ C β`
  set C := (1 + ε₁) / σ with hC
  have hY : (0 : ℝ) < (bohr Γ ρ).card := by exact_mod_cast bohr_card_pos hρ.le
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  have hμT : ∀ x, mu T x ≤ C * β x := by
    intro x
    by_cases hx : x ∈ T
    · have h1 : mu T x ≤ σ⁻¹ * mu (bohr Γ ρ) x := by
        rw [mu_apply, if_pos hx, mu_apply, if_pos (hT hx)]
        rw [← mul_inv, inv_le_inv₀ hTc (by positivity)]; linarith
      have h2 := hreg.mu_le_conv hρ.le hκ hε₁ hνnn hν1 hνsupp x
      calc mu T x ≤ σ⁻¹ * mu (bohr Γ ρ) x := h1
        _ ≤ σ⁻¹ * ((1 + ε₁) * β x) := by gcongr
        _ = C * β x := by rw [hC]; ring
    · rw [mu_apply, if_neg hx]; exact mul_nonneg (by positivity) (hβnn x)
  have h2C : 2 * C ≤ 4 / σ := by
    rw [hC]; rw [show 4 / σ = 2 * (2 / σ) by ring]; gcongr; linarith
  -- The set of large Fourier coefficients of `μ_{B₀}`.
  set S := univ.filter (fun ψ : ZMod N => 1 / 3 ≤ ‖ft (mu B₀) ψ‖) with hS
  set Spec := univ.filter (fun γ : ZMod N => 1 / 2 ≤ ‖ft (mu T) γ‖) with hSpec
  have hftβ : ∀ ψ ∉ S, ‖ft β ψ‖ ≤ (1 / 3) ^ L := by
    intro ψ hψ
    have hψ' : ‖ft (mu B₀) ψ‖ < 1 / 3 := by simpa [hS] using hψ
    rw [hβ, ft_conv, hν, ft_iconv, norm_mul, norm_pow]
    calc ‖ft (mu B₀) ψ‖ ^ L * ‖ft (mu Yp) ψ‖ ≤ (1 / 3) ^ L * 1 := by
          gcongr
          exact norm_ft_mu_le _ hYpne ψ
      _ = (1 / 3) ^ L := mul_one _
  -- Any relatively dissociated subset of the spectrum of size `≤ L` is small.
  have hsmall : ∀ Δ ⊆ Spec, Δ.card ≤ L → SDissoc S Δ → Δ.card < L := by
    intro Δ hΔ hΔL hdis
    have hη : ∀ ε : Δ → Fin 3, ε ≠ (fun _ => 0) → ‖ft β (comb Δ ε)‖ ≤ (1 / 3) ^ L := by
      intro ε hε
      apply hftβ
      rw [comb_eq_sum]
      apply hdis
      by_contra hcon
      push_neg at hcon
      apply hε
      funext z
      have := hcon z.1 z.2
      simpa [z.2] using this
    have h3 : (3 : ℝ) ^ Δ.card * (1 / 3) ^ L ≤ 1 := by
      rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) hΔL
    have hb := chang_bound hTne hβnn hβ1 hμT Δ (fun l hl => by simpa [hSpec] using hΔ hl)
      (by positivity) hη h3
    have : (Δ.card : ℝ) / 8 ≤ Real.log (4 / σ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]; linarith
    have : (Δ.card : ℝ) < L := by linarith
    exact_mod_cast this
  -- choose a maximal one
  set cand := Spec.powerset.filter (fun Δ => Δ.card ≤ L ∧ SDissoc S Δ) with hcand
  have hcandne : cand.Nonempty := ⟨∅, by
    rw [hcand, mem_filter, mem_powerset]
    exact ⟨empty_subset _, by simp, fun E ⟨z, hz, _⟩ => absurd hz (by simp)⟩⟩
  obtain ⟨Δ, hΔmem, hΔmax⟩ := exists_max_image cand card hcandne
  rw [hcand, mem_filter, mem_powerset] at hΔmem
  obtain ⟨hΔSpec, hΔL, hΔdis⟩ := hΔmem
  have hΔlt := hsmall Δ hΔSpec hΔL hΔdis
  refine ⟨Δ, hΔL, fun γ hγ ρ' t ht htΔ => ?_⟩
  have hγSpec : γ ∈ Spec := by rw [hSpec, mem_filter]; exact ⟨mem_univ _, hγ⟩
  have hz : ∀ z ∈ Δ, ‖ech (z * t) - 1‖ ≤ 2 * Real.pi * ρ' := by
    intro z hz
    refine (norm_ech_sub_one_le _).trans ?_
    have := (mem_bohr.1 htΔ) z hz
    gcongr
  have hΔsum : ∀ E : ZMod N → Fin 3,
      ‖ech ((∑ z ∈ Δ, (cf (E z) : ZMod N) * z) * t) - 1‖ ≤ Δ.card * (2 * Real.pi * ρ') := by
    intro E
    rw [sum_mul]
    refine (norm_ech_sum_sub_one_le _ _).trans ?_
    calc ∑ z ∈ Δ, ‖ech ((cf (E z) : ZMod N) * z * t) - 1‖
        ≤ ∑ z ∈ Δ, 2 * Real.pi * ρ' := by
          refine sum_le_sum fun z hz' => ?_
          rw [mul_assoc]
          exact (norm_ech_cf_mul_sub_one_le _ _).trans (hz z hz')
      _ = Δ.card * (2 * Real.pi * ρ') := by rw [sum_const, nsmul_eq_mul]
  have hS6 : ∀ ψ ∈ S, ‖ech (ψ * t) - 1‖ ≤ 6 * ε₀ := by
    intro ψ hψ
    have hψ' : 1 / 3 ≤ ‖ft (mu B₀) ψ‖ := by simpa [hS] using hψ
    have htr := hreg₀.sum_abs_translate_le hρ₀.le hκ₀ hε₀ ht
    have hdiff : ft (fun x => mu B₀ (x - t) - mu B₀ x) ψ = (ech (-(ψ * t)) - 1) * ft (mu B₀) ψ := by
      rw [ft_sub, ft_translate]; ring
    have h1 : ‖ech (-(ψ * t)) - 1‖ * ‖ft (mu B₀) ψ‖ ≤ 2 * ε₀ := by
      rw [← norm_mul, ← hdiff]
      exact (norm_ft_le _ _).trans htr
    rw [← norm_ech_neg_sub_one]
    have h0 : 0 ≤ ‖ech (-(ψ * t)) - 1‖ := norm_nonneg _
    nlinarith
  by_cases hγΔ : γ ∈ Δ
  · refine (hz γ hγΔ).trans ?_
    have : (1 : ℝ) ≤ Δ.card := by exact_mod_cast card_pos.2 ⟨γ, hγΔ⟩
    have : 0 ≤ 2 * Real.pi * ρ' := by
      have := hz γ hγΔ; have := norm_nonneg (ech (γ * t) - 1); linarith
    nlinarith
  -- `insert γ Δ` is not relatively dissociated
  have hnot : ¬ SDissoc S (insert γ Δ) := by
    intro hdis
    have hmem : insert γ Δ ∈ cand := by
      rw [hcand, mem_filter, mem_powerset]
      refine ⟨insert_subset hγSpec hΔSpec, ?_, hdis⟩
      rw [card_insert_of_notMem hγΔ]; omega
    have := hΔmax _ hmem
    rw [card_insert_of_notMem hγΔ] at this; omega
  unfold SDissoc at hnot
  push_neg at hnot
  obtain ⟨E, hEne, hEmem⟩ := hnot
  rw [sum_insert hγΔ] at hEmem
  set R := ∑ z ∈ Δ, (cf (E z) : ZMod N) * z with hR
  have hEγ : E γ ≠ 0 := by
    intro h0
    apply hΔdis E
    · obtain ⟨z, hz', hEz⟩ := hEne
      rcases mem_insert.1 hz' with rfl | hz''
      · exact absurd h0 hEz
      · exact ⟨z, hz'', hEz⟩
    · rw [h0] at hEmem; simpa [cf, hR] using hEmem
  set ψ := (cf (E γ) : ZMod N) * γ + R with hψ
  have hψS := hS6 ψ hEmem
  have hγt : ‖ech (γ * t) - 1‖ = ‖ech ((cf (E γ) : ZMod N) * γ * t) - 1‖ := by
    have : E γ = 1 ∨ E γ = 2 := by
      revert hEγ; generalize E γ = j; fin_cases j <;> simp
    rcases this with h | h
    · rw [h]; simp [cf]
    · rw [h]; simp [cf]; rw [← norm_ech_neg_sub_one, ← neg_mul]
  have hsplit : (cf (E γ) : ZMod N) * γ * t = ψ * t + -(R * t) := by rw [hψ]; ring
  rw [hγt, hsplit]
  refine (norm_ech_add_sub_one_le _ _).trans ?_
  rw [norm_ech_neg_sub_one]
  exact add_le_add hψS (hΔsum E)

end

end KM

end KMFile_LocalChang

section KMFile_GenImp



/-!
# The bootstrapped density increment (Bloom–Sisask, Lemma genimp)
-/

open Finset
open ComplexConjugate
open scoped Pointwise

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma mu_image_sub (T : Finset (ZMod N)) (z x : ZMod N) :
    mu (T.image (· - z)) x = mu T (x + z) := by
  have hc : (T.image (· - z)).card = T.card := card_image_of_injective _ (sub_left_injective)
  have hm : x ∈ T.image (· - z) ↔ x + z ∈ T := by
    rw [mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro h; exact ⟨x + z, h, by abel⟩
  simp only [mu_apply, hc, hm]

lemma norm_ft_mu_image_sub (T : Finset (ZMod N)) (z γ : ZMod N) :
    ‖ft (mu (T.image (· - z))) γ‖ = ‖ft (mu T) γ‖ := by
  have : mu (T.image (· - z)) = fun x => mu T (x - (-z)) := by
    funext x; rw [mu_image_sub, sub_neg_eq_add]
  rw [this, ft_translate, norm_mul, norm_ech, one_mul]

lemma sum_norm_ft_mu_sq {A : Finset (ZMod N)} (hA : A.Nonempty) :
    (N : ℝ)⁻¹ * ∑ γ, ‖ft (mu A) γ‖ ^ 2 = (A.card : ℝ)⁻¹ := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [parseval, sum_sq_mu hA]; field_simp

lemma mu_bohr_neg (Γ : Finset (ZMod N)) (ρ : ℝ) (x : ZMod N) :
    mu (bohr Γ ρ) (-x) = mu (bohr Γ ρ) x := by
  simp only [mu_apply, neg_mem_bohr_iff]

/-- Averaging `μ_A ○ μ_A` against a smoothed probability measure is bounded by the maximal density
of `A` on translates of the Bohr set. -/
lemma sum_conv_mul_dconv_le {A : Finset (ZMod N)} (hA : A.Nonempty) (Γ : Finset (ZMod N))
    (ρ : ℝ) {W : ZMod N → ℝ} (hW : ∀ x, 0 ≤ W x) (hW1 : ∑ x, W x = 1) {Mx : ℝ}
    (hMx : ∀ x, conv (mu A) (mu (bohr Γ ρ)) x ≤ Mx) :
    ∑ x, conv (mu (bohr Γ ρ)) W x * dconv (mu A) (mu A) x ≤ Mx := by
  set B := bohr Γ ρ
  have e : ∑ x, conv (mu B) W x * dconv (mu A) (mu A) x =
      ∑ y, mu A y * ∑ w, W w * conv (mu A) (mu B) (y + w) := by
    simp only [dconv_apply, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [conv_comm (mu B) W]
    simp only [conv_apply, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun w _ => ?_
    rw [← Fintype.sum_equiv (Equiv.subRight y) _ _ (fun x => rfl)]
    refine sum_congr rfl fun u _ => ?_
    simp only [Equiv.subRight_apply, sub_add_cancel]
    rw [show u - y - w = -(y + w - u) by abel, mu_bohr_neg]
    ring
  rw [e]
  calc ∑ y, mu A y * ∑ w, W w * conv (mu A) (mu B) (y + w)
      ≤ ∑ y, mu A y * ∑ w, W w * Mx := by
        refine sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (mu_nonneg A y)
        exact sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hMx _) (hW w)
    _ = Mx := by
        have : ∑ w, W w * Mx = Mx := by rw [← sum_mul, hW1, one_mul]
        rw [this, ← sum_mul, sum_mu hA, one_mul]

/-- **Bootstrapped increment lemma** (Bloom–Sisask). -/
theorem gen_increment {A A₁ A₂ S : Finset (ZMod N)} (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) {ε M : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) (hM : 0 < M)
    (h1 : 1 - ε ≤ ∑ x, dconv (mu A₁) (mu A₂) x * ind S x)
    (h2 : ∀ x ∈ S, (1 + 2 * ε) * M ≤ dconv (mu A) (mu A) x)
    {Γ : Finset (ZMod N)} {ρY κY εY : ℝ} (hρY : 0 < ρY) (hκY : 0 ≤ κY) (hεY : 0 ≤ εY)
    (hεY1 : εY ≤ 1) (hregY : IsReg Γ ρY κY εY)
    {K : ℝ} (hK : ((A₂ + bohr Γ ρY).card : ℝ) ≤ K * A₂.card)
    {r : ℕ} (hr : 1 ≤ r) (hS : (S.card : ℝ) ≤ 4 ^ r * A₁.card) {k : ℕ} (hk : 1 ≤ k)
    {ρ₀ κ₀ ε₀ : ℝ} (hρ₀ : 0 < ρ₀) (hκ₀ : 0 ≤ κ₀) (hε₀ : 0 ≤ ε₀) (hreg₀ : IsReg Γ ρ₀ κ₀ ε₀)
    {Lc : ℕ} (hLρ : Lc * ρ₀ ≤ κY * ρY)
    (hL : 8 * Real.log (8 * K ^ csM r (ε / 4 / (2 * k))) < Lc)
    {ν₀ : ℝ} (hν₀ : (ν₀ + 2 * (1 / 2) ^ k) / A.card ≤ ε * M / 4) :
    ∃ Δ : Finset (ZMod N), Δ.card ≤ Lc ∧ ∀ ρ₃ : ℝ, 0 ≤ ρ₃ → ρ₃ ≤ κ₀ * ρ₀ →
      6 * ε₀ + Lc * (2 * Real.pi * ρ₃) ≤ ν₀ →
        ∃ x, (1 + ε / 4) * M ≤ conv (mu A) (mu (bohr (Γ ∪ Δ) ρ₃)) x := by
  set Y := bohr Γ ρY with hYdef
  have hYne : Y.Nonempty := bohr_nonempty hρY.le
  set m := csM r (ε / 4 / (2 * k)) with hm
  set D := dconv (mu A₁) (mu A₂) with hD
  set FA := dconv (mu A) (mu A) with hFA
  have hK0 : 0 < K := by
    have h1 : (A₂.card : ℝ) ≤ (A₂ + Y).card := by
      obtain ⟨y, hy⟩ := hYne
      exact_mod_cast card_le_card_of_injOn (· + y) (fun a ha => add_mem_add ha hy)
        (fun a _ b _ h => by simpa using h)
    have : (0 : ℝ) < A₂.card := by exact_mod_cast hA₂.card_pos
    nlinarith
  -- almost periodicity
  obtain ⟨T, hTY, hTc, hTap⟩ := linf_almost_periodic hA₁ hA₂ hYne hK hr hS hk
    (by positivity : 0 < ε / 4)
  have hTne : T.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < Y.card / (2 * K ^ m) := by
      have : (0 : ℝ) < Y.card := by exact_mod_cast hYne.card_pos
      positivity
    exact_mod_cast this.trans_le hTc
  obtain ⟨z, hz⟩ := hTne
  obtain ⟨-, hap⟩ := hTap z hz
  set X := T.image (· - z) with hX
  have hXne : X.Nonempty := ⟨0, mem_image.2 ⟨z, hz, sub_self z⟩⟩
  set W := conv (iconv (mu X) k) D with hW
  have hWnn : ∀ x, 0 ≤ W x := conv_nonneg (iconv_nonneg (mu_nonneg' X) k)
    (dconv_nonneg (mu_nonneg' A₁) (mu_nonneg' A₂))
  have hW1 : ∑ x, W x = 1 := by
    rw [hW, sum_conv, sum_iconv (sum_mu hXne), hD, sum_dconv, sum_mu hA₁, sum_mu hA₂]; ring
  have hWS : 1 - 5 * ε / 4 ≤ ∑ x, W x * ind S x := by
    have := (abs_le.1 hap).1; linarith
  have hFAnn : ∀ x, 0 ≤ FA x := dconv_nonneg (mu_nonneg' A) (mu_nonneg' A)
  have hPsi0 : (1 + ε / 2) * M ≤ ∑ x, W x * FA x := by
    have hd : 0 ≤ M * ε * (1 / 4 - 5 * ε / 2) := by
      apply mul_nonneg; positivity; linarith
    calc (1 + ε / 2) * M ≤ (1 + 2 * ε) * M * (1 - 5 * ε / 4) := by nlinarith [hd]
      _ ≤ (1 + 2 * ε) * M * ∑ x, W x * ind S x := by gcongr
      _ = ∑ x, W x * ((1 + 2 * ε) * M * ind S x) := by rw [mul_sum]; congr 1; ext x; ring
      _ ≤ ∑ x, W x * FA x := by
          refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hWnn x)
          rw [ind_apply]; split_ifs with hx
          · rw [mul_one]; exact h2 x hx
          · rw [mul_zero]; exact hFAnn x
  -- Chang
  have hσ : 0 < 1 / (2 * K ^ m) := by positivity
  have hTσ : 1 / (2 * K ^ m) * Y.card ≤ T.card := by
    rw [one_div_mul_eq_div]; exact hTc
  have hL' : 8 * Real.log (4 / (1 / (2 * K ^ m))) < Lc := by
    rw [div_div_eq_mul_div, div_one, show 4 * (2 * K ^ m) = 8 * K ^ m by ring]; exact hL
  obtain ⟨Δ, hΔL, hΔ⟩ := local_chang hρY hκY hεY hεY1 hregY hTY ⟨z, hz⟩ hσ hTσ hρ₀ hκ₀ hε₀
    hreg₀ hLρ hL'
  refine ⟨Δ, hΔL, fun ρ₃ hρ₃0 hρ₃ hν => ?_⟩
  set B₃ := bohr (Γ ∪ Δ) ρ₃ with hB₃
  set Ψ := dconv FA W with hΨ
  have hΨ0 : Ψ 0 = ∑ x, W x * FA x := by
    rw [hΨ, dconv_apply]; refine sum_congr rfl fun x _ => ?_; rw [zero_add, mul_comm]
  -- Fourier estimate of the variation of `Ψ` on `B₃`
  have hvar : ∀ t ∈ B₃, |Ψ t - Ψ 0| ≤ ε * M / 4 := by
    intro t ht
    rw [hB₃, bohr_union, mem_inter] at ht
    have htΓ : t ∈ bohr Γ (κ₀ * ρ₀) := bohr_mono hρ₃ ht.1
    have hpt : ∀ γ, ‖ft Ψ γ‖ * ‖ech (γ * t) - 1‖ ≤ ‖ft (mu A) γ‖ ^ 2 * (ν₀ + 2 * (1 / 2) ^ k) := by
      intro γ
      have hft : ‖ft Ψ γ‖ ≤ ‖ft (mu A) γ‖ ^ 2 * ‖ft (mu T) γ‖ ^ k := by
        rw [hΨ, ft_dconv, hFA, ft_dconv, hW, ft_conv, ft_iconv, hD, ft_dconv]
        simp only [norm_mul, Complex.norm_conj, norm_pow]
        rw [hX, norm_ft_mu_image_sub]
        have ha1 := norm_ft_mu_le A₁ hA₁ γ
        have ha2 := norm_ft_mu_le A₂ hA₂ γ
        have h12 : ‖ft (mu A₁) γ‖ * ‖ft (mu A₂) γ‖ ≤ 1 :=
          mul_le_one₀ ha1 (norm_nonneg _) ha2
        calc ‖ft (mu A) γ‖ * ‖ft (mu A) γ‖ * (‖ft (mu T) γ‖ ^ k *
              (‖ft (mu A₁) γ‖ * ‖ft (mu A₂) γ‖)) ≤ ‖ft (mu A) γ‖ * ‖ft (mu A) γ‖ *
              (‖ft (mu T) γ‖ ^ k * 1) := by gcongr
          _ = ‖ft (mu A) γ‖ ^ 2 * ‖ft (mu T) γ‖ ^ k := by ring
      have hTle : ‖ft (mu T) γ‖ ≤ 1 := norm_ft_mu_le T ⟨z, hz⟩ γ
      have hech2 : ‖ech (γ * t) - 1‖ ≤ 2 := by
        calc ‖ech (γ * t) - 1‖ ≤ ‖ech (γ * t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_ech, norm_one]; norm_num
      have hν0 : 0 ≤ ν₀ := le_trans (by positivity) hν
      have hkey : ‖ft (mu T) γ‖ ^ k * ‖ech (γ * t) - 1‖ ≤ ν₀ + 2 * (1 / 2) ^ k := by
        by_cases hspec : 1 / 2 ≤ ‖ft (mu T) γ‖
        · have hc := hΔ γ hspec ρ₃ t htΓ ht.2
          have hc' : ‖ech (γ * t) - 1‖ ≤ ν₀ := by
            refine hc.trans (le_trans ?_ hν)
            gcongr
          have h1 : ‖ft (mu T) γ‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hTle
          calc ‖ft (mu T) γ‖ ^ k * ‖ech (γ * t) - 1‖ ≤ 1 * ν₀ :=
                mul_le_mul h1 hc' (norm_nonneg _) zero_le_one
            _ ≤ ν₀ + 2 * (1 / 2) ^ k := by
                have : (0:ℝ) ≤ 2 * (1 / 2) ^ k := by positivity
                linarith
        · push_neg at hspec
          have h1 : ‖ft (mu T) γ‖ ^ k ≤ (1 / 2) ^ k := pow_le_pow_left₀ (norm_nonneg _) hspec.le k
          calc ‖ft (mu T) γ‖ ^ k * ‖ech (γ * t) - 1‖ ≤ (1 / 2) ^ k * 2 :=
                mul_le_mul h1 hech2 (norm_nonneg _) (by positivity)
            _ ≤ ν₀ + 2 * (1 / 2) ^ k := by linarith
      calc ‖ft Ψ γ‖ * ‖ech (γ * t) - 1‖ ≤ ‖ft (mu A) γ‖ ^ 2 * ‖ft (mu T) γ‖ ^ k *
            ‖ech (γ * t) - 1‖ := by gcongr
        _ = ‖ft (mu A) γ‖ ^ 2 * (‖ft (mu T) γ‖ ^ k * ‖ech (γ * t) - 1‖) := by ring
        _ ≤ ‖ft (mu A) γ‖ ^ 2 * (ν₀ + 2 * (1 / 2) ^ k) := by gcongr
    have := abs_sub_translate_le Ψ 0 t
    rw [zero_add] at this
    refine this.trans ?_
    calc (N : ℝ)⁻¹ * ∑ γ, ‖ft Ψ γ‖ * ‖ech (γ * t) - 1‖
        ≤ (N : ℝ)⁻¹ * ∑ γ, ‖ft (mu A) γ‖ ^ 2 * (ν₀ + 2 * (1 / 2) ^ k) := by
          exact mul_le_mul_of_nonneg_left (sum_le_sum fun γ _ => hpt γ) (by positivity)
      _ = (ν₀ + 2 * (1 / 2) ^ k) * ((N : ℝ)⁻¹ * ∑ γ, ‖ft (mu A) γ‖ ^ 2) := by
          rw [← sum_mul]; ring
      _ = (ν₀ + 2 * (1 / 2) ^ k) / A.card := by rw [sum_norm_ft_mu_sq hA]; ring
      _ ≤ ε * M / 4 := hν₀
  -- average over `B₃`
  have hB₃ne : B₃.Nonempty := bohr_nonempty hρ₃0
  have havg : (1 + ε / 4) * M ≤ ∑ x, conv (mu B₃) W x * FA x := by
    have e : ∑ x, conv (mu B₃) W x * FA x = ∑ t, mu B₃ t * Ψ t := by
      rw [sum_conv_mul]
      refine sum_congr rfl fun t _ => ?_
      congr 1
      rw [hΨ, dconv_apply]
      refine sum_congr rfl fun x _ => ?_
      rw [add_comm, mul_comm]
    rw [e]
    calc (1 + ε / 4) * M ≤ ∑ t, mu B₃ t * (Ψ 0 - ε * M / 4) := by
          rw [← sum_mul, sum_mu hB₃ne, one_mul, hΨ0]; linarith
      _ ≤ ∑ t, mu B₃ t * Ψ t := by
          refine sum_le_sum fun t _ => ?_
          by_cases ht : t ∈ B₃
          · exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hvar t ht)).1])
              (mu_nonneg _ _)
          · simp [mu_apply, ht]
  by_contra hcon
  push_neg at hcon
  obtain ⟨x0, -, hx0⟩ := exists_max_image univ (fun x => conv (mu A) (mu B₃) x) univ_nonempty
  have hle := sum_conv_mul_dconv_le hA (Γ ∪ Δ) ρ₃ hWnn hW1
    (Mx := conv (mu A) (mu B₃) x0) (fun x => hx0 x (mem_univ x))
  have := hcon x0
  linarith

end

end KM

end KMFile_GenImp

section KMFile_Count



/-!
# Counting three-term progressions in a dense subset of a regular Bohr set
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

/-- `A` contains only trivial solutions of `a + c = 2b`. -/
def Tri (A : Finset (ZMod N)) : Prop := ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + c = b + b → a = b

lemma Tri.mono {A A' : Finset (ZMod N)} (h : Tri A) (hA' : A' ⊆ A) : Tri A' :=
  fun a ha b hb c hc e => h a (hA' ha) b (hA' hb) c (hA' hc) e

lemma Tri.image_sub {A : Finset (ZMod N)} (h : Tri A) (x : ZMod N) : Tri (A.image (· - x)) := by
  intro a ha b hb c hc e
  simp only [mem_image] at ha hb hc
  obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨b, hb, rfl⟩ := hb; obtain ⟨c, hc, rfl⟩ := hc
  have := h a ha b hb c hc (by linear_combination e)
  rw [this]

lemma dconv_mu_mu_apply (A B : Finset (ZMod N)) (x : ZMod N) :
    dconv (mu A) (mu B) x = ((A.card : ℝ) * B.card)⁻¹ * (A.filter fun a => a - x ∈ B).card := by
  rw [dconv_apply]
  rw [← sum_add_right _ (-x)]
  simp only [add_neg_cancel_comm_assoc]
  have : ∀ y, mu A y * mu B (y + -x) = mu A y * mu B (y - x) := fun y => by rw [sub_eq_add_neg]
  simp_rw [this, sum_mu_mul]
  have h2 : ∑ a ∈ A, mu B (a - x) = ∑ a ∈ A, if a - x ∈ B then (B.card : ℝ)⁻¹ else 0 := by
    simp [mu_apply]
  rw [h2, ← sum_filter, sum_const, nsmul_eq_mul, mul_inv]
  ring

lemma dconv_swap (f g : ZMod N → ℝ) (x : ZMod N) : dconv f g x = dconv g f (-x) := by
  rw [dconv_apply, dconv_apply]
  conv_rhs => rw [← sum_add_right _ x]
  refine sum_congr rfl fun y _ => ?_
  rw [show -x + (y + x) = y by abel, add_comm y x, mul_comm]

lemma conv_mu_bohr_eq_dconv (f : ZMod N → ℝ) (Γ : Finset (ZMod N)) (ρ : ℝ) (x : ZMod N) :
    conv f (mu (bohr Γ ρ)) x = dconv f (mu (bohr Γ ρ)) x := by
  rw [conv_apply, dconv_apply, ← sum_add_right _ x]
  refine sum_congr rfl fun y _ => ?_
  rw [add_comm y x, show x - (x + y) = -y by abel, mu_bohr_neg]

/-- For `y` in the `κ`-dilate, few elements of `A ⊆ bohr Γ ρ` leave the Bohr set when shifted by
`y`. -/
lemma card_filter_sub_mem_ge {Γ : Finset (ZMod N)} {ρ κ ε : ℝ} (hreg : IsReg Γ ρ κ ε)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {A : Finset (ZMod N)} (hA : A ⊆ bohr Γ ρ)
    {y : ZMod N} (hy : y ∈ bohr Γ (κ * ρ)) :
    (A.card : ℝ) - ε * (bohr Γ ρ).card ≤ (A.filter fun a => a - y ∈ bohr Γ ρ).card := by
  set B := bohr Γ ρ
  have hs := hreg.card_sdiff_le hρ hκ hε hy
  have hsub : A.filter (fun a => a - y ∉ B) ⊆ B.filter (fun x => x - y ∉ B) := by
    intro a ha; rw [mem_filter] at *; exact ⟨hA ha.1, ha.2⟩
  have h1 : ((A.filter fun a => a - y ∉ B).card : ℝ) ≤ ε * B.card :=
    le_trans (by exact_mod_cast card_le_card hsub) hs
  have h2 := card_filter_add_card_filter_not (s := A) (fun a => a - y ∈ B)
  have : ((A.filter fun a => a - y ∈ B).card : ℝ) + (A.filter fun a => a - y ∉ B).card =
      A.card := by exact_mod_cast h2
  linarith

/-- Two-sided bounds for `μ_A ○ μ_B` on the `κ`-dilate of a regular Bohr set `B ⊇ A`. -/
lemma dconv_mu_bohr_bounds {Γ : Finset (ZMod N)} {ρ κ ε : ℝ} (hreg : IsReg Γ ρ κ ε)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {A : Finset (ZMod N)} (hA : A ⊆ bohr Γ ρ)
    (hAne : A.Nonempty) {y : ZMod N} (hy : y ∈ bohr Γ (κ * ρ)) :
    ((bohr Γ ρ).card : ℝ)⁻¹ - ε / A.card ≤ dconv (mu A) (mu (bohr Γ ρ)) y ∧
      dconv (mu A) (mu (bohr Γ ρ)) y ≤ ((bohr Γ ρ).card : ℝ)⁻¹ := by
  set B := bohr Γ ρ
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast bohr_card_pos hρ
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  rw [dconv_mu_mu_apply]
  have hlow := card_filter_sub_mem_ge hreg hρ hκ hε hA hy
  have hup : ((A.filter fun a => a - y ∈ B).card : ℝ) ≤ A.card := by
    exact_mod_cast card_filter_le _ _
  constructor
  · calc (B.card : ℝ)⁻¹ - ε / A.card = ((A.card : ℝ) * B.card)⁻¹ * (A.card - ε * B.card) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  · calc ((A.card : ℝ) * B.card)⁻¹ * (A.filter fun a => a - y ∈ B).card
        ≤ ((A.card : ℝ) * B.card)⁻¹ * A.card := mul_le_mul_of_nonneg_left hup (by positivity)
      _ = (B.card : ℝ)⁻¹ := by field_simp

/-- The self-convolution of a `Tri` set at a doubled point. -/
lemma conv_mu_self_double {A : Finset (ZMod N)} (hT : Tri A) {b : ZMod N} (hb : b ∈ A) :
    conv (mu A) (mu A) (b + b) = ((A.card : ℝ) ^ 2)⁻¹ := by
  rw [conv_apply]
  have h1 : ∀ y, mu A y * mu A (b + b - y) =
      if y ∈ A.filter (fun a => b + b - a ∈ A) then ((A.card : ℝ) ^ 2)⁻¹ else 0 := by
    intro y
    simp only [mu_apply, mem_filter]
    split_ifs <;> simp_all [sq]
  simp_rw [h1]
  rw [sum_ite_mem, univ_inter, sum_const]
  have : A.filter (fun a => b + b - a ∈ A) = {b} := by
    ext a
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨ha, hc⟩; exact hT a ha b hb _ hc (by ring)
    · rintro rfl; exact ⟨hb, by simpa using hb⟩
  rw [this, card_singleton, one_smul]

lemma conv_self_sub_expand (A B : Finset (ZMod N)) (y : ZMod N) :
    conv (fun x => mu A x - mu B x) (fun x => mu A x - mu B x) y =
      conv (mu A) (mu A) y - 2 * conv (mu A) (mu B) y + conv (mu B) (mu B) y := by
  have h := congrFun (conv_comm (mu A) (mu B)) y
  simp only [conv_apply] at *
  simp only [sub_mul, mul_sub, sum_sub_distrib]
  linarith

lemma dconv_self_sub_expand (A B : Finset (ZMod N)) (y : ZMod N) :
    dconv (fun x => mu A x - mu B x) (fun x => mu A x - mu B x) y =
      dconv (mu A) (mu A) y - dconv (mu A) (mu B) y - dconv (mu A) (mu B) (-y) +
        dconv (mu B) (mu B) y := by
  have h := dconv_swap (mu B) (mu A) y
  simp only [dconv_apply] at *
  simp only [sub_mul, mul_sub, sum_sub_distrib]
  linarith

/-- **3AP count.** For a `Tri` set `A₁` dense in a regular Bohr set `B` which is not too small,
the balanced self-convolution is very negative on average over `C = 2 ⬝ A₂`. -/
theorem count_bound {Γ : Finset (ZMod N)} {ρ κ ε : ℝ} (hreg : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {A₁ A₂ : Finset (ZMod N)} (hA₁ : A₁ ⊆ bohr Γ ρ) (hT : Tri A₁)
    (hA₂ : A₂ ⊆ A₁) (hA₂ne : A₂.Nonempty) (hA₂B : ∀ b ∈ A₂, b + b ∈ bohr Γ (κ * ρ)) {α : ℝ}
    (hα : 0 < α) (hA₁c : α * (bohr Γ ρ).card ≤ A₁.card) (hB : 4 ≤ α ^ 2 * (bohr Γ ρ).card)
    (hε8 : 8 * ε ≤ α) :
    ∑ y, mu (A₂.image fun b => b + b) y *
      conv (fun x => mu A₁ x - mu (bohr Γ ρ) x) (fun x => mu A₁ x - mu (bohr Γ ρ) x) y ≤
        -(1 / (2 * (bohr Γ ρ).card)) := by
  set B := bohr Γ ρ
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast bohr_card_pos hρ
  have hA₁ne : A₁.Nonempty := hA₂ne.mono hA₂
  have hAc : (0 : ℝ) < A₁.card := by exact_mod_cast hA₁ne.card_pos
  set V : ℝ := ((A₁.card : ℝ) ^ 2)⁻¹ - 2 * ((B.card : ℝ)⁻¹ - ε / A₁.card) + (B.card : ℝ)⁻¹
  have hpt : ∀ y ∈ A₂.image (fun b => b + b),
      conv (fun x => mu A₁ x - mu B x) (fun x => mu A₁ x - mu B x) y ≤ V := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
    rw [conv_self_sub_expand, conv_mu_self_double hT (hA₂ hb), conv_mu_bohr_eq_dconv,
      conv_mu_bohr_eq_dconv]
    have h1 := dconv_mu_bohr_bounds hreg hρ hκ hε hA₁ hA₁ne (hA₂B b hb)
    have h2 := dconv_mu_bohr_bounds hreg hρ hκ hε (subset_refl B) (bohr_nonempty hρ) (hA₂B b hb)
    linarith [h1.1, h2.2]
  have hCne : (A₂.image fun b => b + b).Nonempty := hA₂ne.image _
  have hCc : (0 : ℝ) < (A₂.image fun b => b + b).card := by exact_mod_cast hCne.card_pos
  have havg : ∑ y, mu (A₂.image fun b => b + b) y *
      conv (fun x => mu A₁ x - mu B x) (fun x => mu A₁ x - mu B x) y ≤ V := by
    rw [sum_mu_mul]
    calc ((A₂.image fun b => b + b).card : ℝ)⁻¹ * ∑ y ∈ A₂.image (fun b => b + b),
          conv (fun x => mu A₁ x - mu B x) (fun x => mu A₁ x - mu B x) y
        ≤ ((A₂.image fun b => b + b).card : ℝ)⁻¹ * ∑ y ∈ A₂.image (fun b => b + b), V := by
          gcongr with y hy; exact hpt y hy
      _ = V := by rw [sum_const, nsmul_eq_mul]; field_simp
  refine havg.trans ?_
  -- algebra
  have hsq : 4 * (B.card : ℝ) ≤ (A₁.card : ℝ) ^ 2 := by
    have : (α * B.card) ^ 2 ≤ (A₁.card : ℝ) ^ 2 := by
      have : 0 ≤ α * B.card := by positivity
      gcongr
    nlinarith
  have e1 : ((A₁.card : ℝ) ^ 2)⁻¹ ≤ 1 / (4 * B.card) := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by positivity) hsq
  have e2 : 2 * (ε / A₁.card) ≤ 1 / (4 * B.card) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    · have : 8 * ε * B.card ≤ α * B.card := by gcongr
      nlinarith
  have e3 : (B.card : ℝ)⁻¹ = 4 * (1 / (4 * B.card)) := by field_simp
  have e4 : 1 / (2 * (B.card : ℝ)) = 2 * (1 / (4 * B.card)) := by field_simp; ring
  simp only [V]
  rw [e4]
  rw [e3]
  linarith

/-- Pointwise error between `|B| (f ○ f) + 1` and `|B| (μ_A ○ μ_A)` on the `κ`-dilate. -/
theorem dconv_error_bound {Γ : Finset (ZMod N)} {ρ κ ε : ℝ} (hreg : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {A : Finset (ZMod N)} (hA : A ⊆ bohr Γ ρ) (hAne : A.Nonempty)
    {α : ℝ} (hα : 0 < α) (hAc : α * (bohr Γ ρ).card ≤ A.card) {x : ZMod N}
    (hx : x ∈ bohr Γ (κ * ρ)) :
    |(bohr Γ ρ).card * dconv (fun x => mu A x - mu (bohr Γ ρ) x)
        (fun x => mu A x - mu (bohr Γ ρ) x) x + 1 -
      (bohr Γ ρ).card * dconv (mu A) (mu A) x| ≤ 2 * ε / α := by
  set B := bohr Γ ρ
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast bohr_card_pos hρ
  have hAc0 : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hAB : (A.card : ℝ) ≤ B.card := by exact_mod_cast card_le_card hA
  have hα1 : α ≤ 1 := by
    by_contra h; push_neg at h; nlinarith
  rw [dconv_self_sub_expand]
  have hx' : -x ∈ bohr Γ (κ * ρ) := neg_mem_bohr hx
  have h1 := dconv_mu_bohr_bounds hreg hρ hκ hε hA hAne hx
  have h2 := dconv_mu_bohr_bounds hreg hρ hκ hε hA hAne hx'
  have h3 := dconv_mu_bohr_bounds hreg hρ hκ hε (subset_refl B) (bohr_nonempty hρ) hx
  have hεA : B.card * (ε / A.card) ≤ ε / α := by
    rw [mul_div_assoc', div_le_div_iff₀ hAc0 hα]
    nlinarith
  have hεB : (B.card : ℝ) * (ε / B.card) = ε := by field_simp
  have hBi : (B.card : ℝ) * (B.card : ℝ)⁻¹ = 1 := by field_simp
  have hεα : ε ≤ ε / α := by rw [le_div_iff₀ hα]; nlinarith
  set a1 := dconv (mu A) (mu B) x
  set a2 := dconv (mu A) (mu B) (-x)
  set a3 := dconv (mu B) (mu B) x
  have k1 : B.card * (B.card : ℝ)⁻¹ - B.card * (ε / A.card) ≤ B.card * a1 := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left h1.1 hBc.le
  have k2 : B.card * (B.card : ℝ)⁻¹ - B.card * (ε / A.card) ≤ B.card * a2 := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left h2.1 hBc.le
  have k3 : B.card * (B.card : ℝ)⁻¹ - B.card * (ε / B.card) ≤ B.card * a3 := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left h3.1 hBc.le
  have u1 : B.card * a1 ≤ B.card * (B.card : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h1.2 hBc.le
  have u2 : B.card * a2 ≤ B.card * (B.card : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h2.2 hBc.le
  have u3 : B.card * a3 ≤ B.card * (B.card : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h3.2 hBc.le
  have hE : (B.card : ℝ) * (dconv (mu A) (mu A) x - a1 - a2 + a3) + 1 -
      B.card * dconv (mu A) (mu A) x = 1 - B.card * a1 - B.card * a2 + B.card * a3 := by ring
  rw [hE, abs_le, mul_div_assoc]
  have hεα0 : 0 ≤ ε / α := div_nonneg hε hα.le
  constructor
  · linarith
  · linarith

end

end KM

end KMFile_Count

section KMFile_Unbalancing



/-!
# Unbalancing

Bloom–Sisask Lemma 7 (unbalancing of spectrally non-negative functions), with the positivity
input proved physically (Shkredov's argument) for `f = g ○ g`, `ν = h ○ h`.
-/

open Finset

namespace KM

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Monotonicity of weighted power means. -/
theorem lpow_mono {ν g : G → ℝ} (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (hg : ∀ x, 0 ≤ g x)
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) {c : ℝ} (hc : 0 ≤ c) (h : c ^ p ≤ ∑ x, ν x * g x ^ p) :
    c ^ q ≤ ∑ x, ν x * g x ^ q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : (1 : ℝ) ≤ (q : ℝ) / p := by
    rw [le_div_iff₀ hp0, one_mul]; exact_mod_cast hpq
  have J := Real.rpow_arith_mean_le_arith_mean_rpow univ ν (fun x => g x ^ p)
    (fun x _ => hν x) hν1 (fun x _ => pow_nonneg (hg x) p) hr
  have e : ∀ t : ℝ, 0 ≤ t → (t ^ p) ^ ((q : ℝ) / p) = t ^ q := by
    intro t ht
    rw [← Real.rpow_natCast t p, ← Real.rpow_mul ht, mul_div_cancel₀ _ hp0.ne', Real.rpow_natCast]
  calc c ^ q = (c ^ p) ^ ((q : ℝ) / p) := (e c hc).symm
    _ ≤ (∑ x, ν x * g x ^ p) ^ ((q : ℝ) / p) :=
        Real.rpow_le_rpow (pow_nonneg hc p) h (by positivity)
    _ ≤ ∑ x, ν x * (g x ^ p) ^ ((q : ℝ) / p) := J
    _ = ∑ x, ν x * g x ^ q := by
        refine sum_congr rfl fun x _ => ?_
        rw [e _ (hg x)]

omit [DecidableEq G] in
lemma dconv_pow_eq (g : G → ℝ) (k : ℕ) (x : G) :
    dconv g g x ^ k = ∑ u : Fin k → G, ∏ i, g (x + u i) * g (u i) := by
  unfold dconv
  rw [← Fin.prod_const k, Fintype.prod_sum]

theorem sum_dconv_mul_dconv_pow_eq (g h : G → ℝ) (k : ℕ) :
    ∑ x, dconv h h x * dconv g g x ^ k =
      ∑ u : Fin k → G, (∑ w, h w * ∏ i, g (w + u i)) ^ 2 := by
  symm
  have e1 : ∀ w y : G, (∑ v, g (w + v) * g (y + v)) = dconv g g (w - y) := by
    intro w y
    unfold dconv
    exact Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun v => by
      simp only [Equiv.coe_addLeft]; rw [show w - y + (y + v) = w + v by abel])
  calc ∑ u : Fin k → G, (∑ w, h w * ∏ i, g (w + u i)) ^ 2
      = ∑ u : Fin k → G, ∑ w, ∑ y, h w * h y * ∏ i, (g (w + u i) * g (y + u i)) := by
        refine sum_congr rfl fun u _ => ?_
        rw [sq, sum_mul_sum]
        refine sum_congr rfl fun w _ => sum_congr rfl fun y _ => ?_
        rw [prod_mul_distrib]; ring
    _ = ∑ w, ∑ y, h w * h y * ∑ u : Fin k → G, ∏ i, (g (w + u i) * g (y + u i)) := by
        rw [sum_comm]
        refine sum_congr rfl fun w _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [mul_sum]
    _ = ∑ w, ∑ y, h w * h y * dconv g g (w - y) ^ k := by
        refine sum_congr rfl fun w _ => sum_congr rfl fun y _ => ?_
        rw [← e1, ← Fin.prod_const, Fintype.prod_sum]
    _ = ∑ y, ∑ x, h (x + y) * h y * dconv g g x ^ k := by
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun w => by simp)
    _ = ∑ x, dconv h h x * dconv g g x ^ k := by
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        rw [dconv_apply (f := h) (g := h), sum_mul]

/-- Shkredov's physical positivity: `⟨h ○ h, (g ○ g)^k⟩ ≥ 0`. -/
theorem sum_dconv_mul_dconv_pow_nonneg (g h : G → ℝ) (k : ℕ) :
    0 ≤ ∑ x, dconv h h x * dconv g g x ^ k := by
  rw [sum_dconv_mul_dconv_pow_eq]; positivity

lemma dconv_self_neg (h : G → ℝ) (x : G) : dconv h h (-x) = dconv h h x := by
  unfold dconv
  exact Fintype.sum_equiv (Equiv.subRight x) _ _ (fun y => by
    simp only [Equiv.subRight_apply]; rw [show x + (y - x) = y by abel,
      show -x + y = y - x by abel, mul_comm])

/-- Physical form of the positive-definiteness comparison: for `ν = h ○ h`, the `p`-th moment of
`f ∗ f` against any translate of `ν` is at most that of `f ○ f` against `ν`. -/
theorem sum_tr_dconv_mul_conv_pow_le (f h : G → ℝ) (p : ℕ) (t : G) :
    ∑ x, dconv h h (x - t) * conv f f x ^ p ≤ ∑ x, dconv h h x * dconv f f x ^ p := by
  set Q := ∑ x, dconv h h x * dconv f f x ^ p with hQ
  let F : (Fin p → G) → ℝ := fun v => ∑ w, h w * ∏ i, f (w + v i)
  let F' : (Fin p → G) → ℝ := fun v => ∑ y, h y * ∏ i, f (t - y - v i)
  have hF : ∑ v, F v ^ 2 = Q := (sum_dconv_mul_dconv_pow_eq f h p).symm
  have hF' : ∑ v, F' v ^ 2 = Q := by
    let fn : G → ℝ := fun z => f (-z)
    have h1 : ∑ v, F' v ^ 2 = ∑ v : Fin p → G, (∑ w, h w * ∏ i, fn (w + v i)) ^ 2 := by
      refine Fintype.sum_equiv (Equiv.addRight (fun _ => -t)) _ _ (fun v => ?_)
      simp only [F', fn, Equiv.coe_addRight, Pi.add_apply]
      congr 1
      refine sum_congr rfl fun y _ => ?_
      congr 1
      refine prod_congr rfl fun i _ => ?_
      congr 1; abel
    rw [h1, ← sum_dconv_mul_dconv_pow_eq fn h p, hQ]
    rw [← sum_neg]
    refine sum_congr rfl fun x _ => ?_
    rw [dconv_self_neg]
    congr 2
    unfold dconv
    simp only [fn]
    exact Fintype.sum_equiv (Equiv.neg G) _ _ (fun y => by
      simp only [Equiv.neg_apply, neg_neg]; rw [show -(-x + y) = x + -y by abel])
  have hQ0 : 0 ≤ Q := sum_dconv_mul_dconv_pow_nonneg f h p
  have hpow : ∀ z : G, conv f f z ^ p = ∑ u : Fin p → G, ∏ i, (f (u i) * f (z - u i)) := by
    intro z
    rw [conv_apply, ← Fin.prod_const, Fintype.prod_sum]
  have hid : ∑ x, dconv h h (x - t) * conv f f x ^ p = ∑ v, F v * F' v := by
    calc ∑ x, dconv h h (x - t) * conv f f x ^ p
        = ∑ y, ∑ x, h (x - t + y) * h y * conv f f x ^ p := by
          simp_rw [dconv_apply (f := h) (g := h), sum_mul]; rw [sum_comm]
      _ = ∑ y, ∑ w, h w * h y * conv f f (w + t - y) ^ p := by
          refine sum_congr rfl fun y _ => ?_
          refine Fintype.sum_equiv (Equiv.subRight (t - y)) _ _ (fun x => ?_)
          simp only [Equiv.subRight_apply]
          rw [show x - (t - y) = x - t + y by abel, show x - t + y + t - y = x by abel]
      _ = ∑ y, ∑ w, h w * h y * ∑ v : Fin p → G, ∏ i, (f (w + v i) * f (t - y - v i)) := by
          refine sum_congr rfl fun y _ => sum_congr rfl fun w _ => ?_
          rw [hpow]
          congr 1
          refine Fintype.sum_equiv (Equiv.subLeft (fun _ => t - y)) _ _ (fun u => ?_)
          simp only [Equiv.subLeft_apply, Pi.sub_apply]
          refine prod_congr rfl fun i _ => ?_
          rw [show t - y - (t - y - u i) = u i by abel, show w + (t - y - u i) = w + t - y - u i by abel]
          ring
      _ = ∑ v, F v * F' v := by
          have hv : ∀ v, F v * F' v =
              ∑ y, ∑ w, h w * h y * ∏ i, (f (w + v i) * f (t - y - v i)) := by
            intro v
            simp only [F, F']
            rw [sum_mul_sum, sum_comm]
            refine sum_congr rfl fun y _ => sum_congr rfl fun w _ => ?_
            rw [prod_mul_distrib]; ring
          simp only [hv, mul_sum]
          calc _ = ∑ y, ∑ v : Fin p → G, ∑ w, h w * h y * ∏ i, (f (w + v i) * f (t - y - v i)) :=
                sum_congr rfl fun y _ => sum_comm
            _ = _ := sum_comm
  rw [hid]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ F F'
  rw [hF, hF'] at hcs
  nlinarith [sq_nonneg (∑ v, F v * F' v - Q), sq_nonneg (∑ v, F v * F' v + Q)]

/-- Exponent produced by the unbalancing lemma. -/
def ubP (q : ℕ) (ε : ℝ) : ℕ := 2 * q * ⌈36 / ε ^ 2⌉₊

/-- **Unbalancing** (Kelley–Meka; Bloom–Sisask Lemma 7), in `p`-th power form. -/
theorem unbalancing {ν f : G → ℝ} (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (hpos : ∀ k : ℕ, 0 ≤ ∑ x, ν x * f x ^ k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {q : ℕ}
    (hq : Odd q) (hq5 : 5 ≤ q) (h : ε ^ q ≤ ∑ x, ν x * |f x| ^ q) :
    (1 + ε / 2) ^ ubP q ε ≤ ∑ x, ν x * (f x + 1) ^ ubP q ε := by
  set M := ⌈36 / ε ^ 2⌉₊ with hM
  have hM1 : 1 ≤ M := by
    rw [hM, Nat.one_le_ceil_iff]; positivity
  have hMge : 36 / ε ^ 2 ≤ M := Nat.le_ceil _
  have hP : ubP q ε = 2 * q * M := rfl
  have hPeven : Even (ubP q ε) := by rw [hP, mul_assoc]; exact even_two_mul _
  have h2qeven : Even (2 * q) := even_two_mul _
  have hq1 : Even (q - 1) := by
    obtain ⟨j, hj⟩ := hq; exact ⟨j, by omega⟩
  -- Step 1: the positive part carries half of the mass.
  set T := univ.filter fun x => 3 * ε / 4 ≤ f x with hT
  have hpowq : ∀ a : ℝ, a ^ q = a ^ (q - 1) * a := by
    intro a; rw [← pow_succ]; congr 1; omega
  have hpospart : ∀ x, 2 * max (f x) 0 * |f x| ^ (q - 1) = f x ^ q + |f x| ^ q := by
    intro x
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx, hpowq]; ring
    · rw [max_eq_right hx, abs_of_nonpos hx, hpowq, hpowq (-f x), Even.neg_pow hq1]; ring
  have hstep1 : ε ^ q / 2 ≤ ∑ x, ν x * (max (f x) 0 * |f x| ^ (q - 1)) := by
    have : ∑ x, ν x * (2 * max (f x) 0 * |f x| ^ (q - 1)) =
        ∑ x, ν x * f x ^ q + ∑ x, ν x * |f x| ^ q := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun x _ => ?_; rw [hpospart]; ring
    have h2 : ∑ x, ν x * (2 * max (f x) 0 * |f x| ^ (q - 1)) =
        2 * ∑ x, ν x * (max (f x) 0 * |f x| ^ (q - 1)) := by
      rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; ring
    linarith [hpos q]
  -- Step 2: restrict to `T`.
  have hpt : ∀ x, max (f x) 0 * |f x| ^ (q - 1) ≤
      ind T x * |f x| ^ q + (3 * ε / 4) ^ q := by
    intro x
    by_cases hxT : x ∈ T
    · have hx : 3 * ε / 4 ≤ f x := by simpa [hT] using hxT
      have hf0 : 0 ≤ f x := by linarith
      rw [ind_apply, if_pos hxT, max_eq_left hf0, abs_of_nonneg hf0, hpowq (f x), one_mul,
        mul_comm]
      have : 0 ≤ (3 * ε / 4) ^ q := by positivity
      linarith
    · have hx : f x < 3 * ε / 4 := by simpa [hT] using hxT
      rw [ind_apply, if_neg hxT, zero_mul, zero_add]
      rcases le_total (f x) 0 with hf0 | hf0
      · rw [max_eq_right hf0, zero_mul]; positivity
      · rw [max_eq_left hf0, abs_of_nonneg hf0, mul_comm, ← hpowq]
        exact pow_le_pow_left₀ hf0 hx.le q
  have h34 : (3 / 4 : ℝ) ^ q ≤ 1 / 4 := by
    calc (3 / 4 : ℝ) ^ q ≤ (3 / 4) ^ 5 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hq5
      _ ≤ 1 / 4 := by norm_num
  have hstep2 : ε ^ q / 4 ≤ ∑ x, ν x * (ind T x * |f x| ^ q) := by
    have : ∑ x, ν x * (max (f x) 0 * |f x| ^ (q - 1)) ≤
        ∑ x, ν x * (ind T x * |f x| ^ q) + (3 * ε / 4) ^ q := by
      calc ∑ x, ν x * (max (f x) 0 * |f x| ^ (q - 1))
          ≤ ∑ x, ν x * (ind T x * |f x| ^ q + (3 * ε / 4) ^ q) :=
            sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hν x)
        _ = _ := by
            simp_rw [mul_add, sum_add_distrib, ← sum_mul, hν1, one_mul]
    have e : (3 * ε / 4) ^ q = (3 / 4) ^ q * ε ^ q := by rw [← mul_pow]; ring
    have : (3 * ε / 4) ^ q ≤ ε ^ q / 4 := by
      rw [e]; nlinarith [pow_pos hε q]
    linarith
  -- Step 3: case analysis on the `2q`-th moment of `f + 1`.
  by_cases hbig : (1 + ε / 2) ^ (2 * q) ≤ ∑ x, ν x * (f x + 1) ^ (2 * q)
  · have hle : 2 * q ≤ ubP q ε := by rw [hP]; nlinarith
    have habs : ∀ n, Even n → ∀ x, (f x + 1) ^ n = |f x + 1| ^ n :=
      fun n hn x => (Even.pow_abs hn _).symm
    have h1 : (1 + ε / 2) ^ (2 * q) ≤ ∑ x, ν x * |f x + 1| ^ (2 * q) := by
      simpa only [habs _ h2qeven] using hbig
    have := lpow_mono hν hν1 (fun x => abs_nonneg (f x + 1)) (by omega) hle
      (by positivity) h1
    simpa only [habs _ hPeven] using this
  push_neg at hbig
  -- `f` has bounded `2q`-th moment.
  have hmom : ∑ x, ν x * f x ^ (2 * q) ≤ 9 ^ q := by
    have hpt2 : ∀ x, f x ^ (2 * q) ≤ 2 ^ (2 * q - 1) * ((f x + 1) ^ (2 * q) + 1) := by
      intro x
      have := Even.add_pow_le (a := f x + 1) (b := -1) h2qeven
      rw [Even.neg_one_pow h2qeven] at this
      simpa using this
    calc ∑ x, ν x * f x ^ (2 * q) ≤ ∑ x, ν x * (2 ^ (2 * q - 1) * ((f x + 1) ^ (2 * q) + 1)) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt2 x) (hν x)
      _ = 2 ^ (2 * q - 1) * (∑ x, ν x * (f x + 1) ^ (2 * q) + 1) := by
          rw [show 2 ^ (2 * q - 1) * (∑ x, ν x * (f x + 1) ^ (2 * q) + 1) =
            2 ^ (2 * q - 1) * (∑ x, ν x * (f x + 1) ^ (2 * q) + ∑ x, ν x) by rw [hν1],
            ← sum_add_distrib, mul_sum]
          refine sum_congr rfl fun x _ => ?_; ring
      _ ≤ 2 ^ (2 * q - 1) * ((3 / 2) ^ (2 * q) + (3 / 2) ^ (2 * q)) := by
          gcongr
          · exact hbig.le.trans (by gcongr; linarith)
          · exact one_le_pow₀ (by norm_num)
      _ = 9 ^ q := by
          have h2 : (2 : ℝ) ^ (2 * q - 1) * 2 = 2 ^ (2 * q) := by
            rw [← pow_succ]; congr 1; omega
          rw [← two_mul, ← mul_assoc, h2, ← mul_pow, pow_mul]
          norm_num
  -- Cauchy–Schwarz: `ν(T)` is not too small.
  set νT := ∑ x, ν x * ind T x with hνT
  have hCS : (∑ x, ν x * (ind T x * |f x| ^ q)) ^ 2 ≤ νT * ∑ x, ν x * f x ^ (2 * q) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (ν x) * ind T x)
      (fun x => Real.sqrt (ν x) * |f x| ^ q)
    have e1 : ∀ x, Real.sqrt (ν x) * ind T x * (Real.sqrt (ν x) * |f x| ^ q) =
        ν x * (ind T x * |f x| ^ q) := by
      intro x; rw [show Real.sqrt (ν x) * ind T x * (Real.sqrt (ν x) * |f x| ^ q) =
        Real.sqrt (ν x) ^ 2 * (ind T x * |f x| ^ q) by ring, Real.sq_sqrt (hν x)]
    have e2 : ∀ x, (Real.sqrt (ν x) * ind T x) ^ 2 = ν x * ind T x := by
      intro x; rw [mul_pow, Real.sq_sqrt (hν x)]
      unfold ind; split_ifs <;> simp
    have e3 : ∀ x, (Real.sqrt (ν x) * |f x| ^ q) ^ 2 = ν x * f x ^ (2 * q) := by
      intro x; rw [mul_pow, Real.sq_sqrt (hν x), ← pow_mul, mul_comm q 2, Even.pow_abs h2qeven]
    simp only [e1, e2, e3] at this
    exact this
  have hνT0 : 0 ≤ νT := sum_nonneg fun x _ => mul_nonneg (hν x) (ind_nonneg T x)
  have hνTlow : ε ^ (2 * q) / 6 ^ (2 * q) ≤ νT := by
    have h1 : (ε ^ q / 4) ^ 2 ≤ νT * 9 ^ q := by
      calc (ε ^ q / 4) ^ 2 ≤ (∑ x, ν x * (ind T x * |f x| ^ q)) ^ 2 := by
            gcongr
        _ ≤ νT * ∑ x, ν x * f x ^ (2 * q) := hCS
        _ ≤ νT * 9 ^ q := mul_le_mul_of_nonneg_left hmom hνT0
    have h16 : (16 : ℝ) ≤ 4 ^ q := by
      calc (16 : ℝ) = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : (6 : ℝ) ^ (2 * q) = 4 ^ q * 9 ^ q := by
      rw [pow_mul, ← mul_pow]; norm_num
    rw [e, div_le_iff₀ (by positivity)]
    have : (ε ^ q / 4) ^ 2 = ε ^ (2 * q) / 16 := by rw [div_pow, ← pow_mul, mul_comm q 2]; norm_num
    rw [this] at h1
    have hε2 : 0 ≤ ε ^ (2 * q) := by positivity
    have h9 : (0:ℝ) < 9 ^ q := by positivity
    nlinarith
  -- Final: growth on `T`.
  have hR : 1 + ε / 6 ≤ (1 + 3 * ε / 4) / (1 + ε / 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hRM : 6 / ε ≤ ((1 + 3 * ε / 4) / (1 + ε / 2)) ^ M := by
    calc 6 / ε ≤ 1 + M * (ε / 6) := by
          have : 36 / ε ^ 2 * (ε / 6) = 6 / ε := by field_simp; ring
          have h' : 36 / ε ^ 2 * (ε / 6) ≤ M * (ε / 6) := by gcongr
          linarith
      _ ≤ (1 + ε / 6) ^ M := one_add_mul_le_pow (by linarith) M
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hR M
  have hfin : (1 + ε / 2) ^ ubP q ε ≤ νT * (1 + 3 * ε / 4) ^ ubP q ε := by
    have hRP : (6 / ε) ^ (2 * q) ≤ ((1 + 3 * ε / 4) / (1 + ε / 2)) ^ ubP q ε := by
      rw [hP, mul_comm (2 * q) M, pow_mul ((1 + 3 * ε / 4) / (1 + ε / 2))]
      exact pow_le_pow_left₀ (by positivity) hRM _
    have hpos1 : (0 : ℝ) < (1 + ε / 2) ^ ubP q ε := by positivity
    have hRP' : (6 / ε) ^ (2 * q) * (1 + ε / 2) ^ ubP q ε ≤ (1 + 3 * ε / 4) ^ ubP q ε := by
      rw [div_pow (1 + 3 * ε / 4), le_div_iff₀ hpos1] at hRP; exact hRP
    have e : ε ^ (2 * q) / 6 ^ (2 * q) * (6 / ε) ^ (2 * q) = 1 := by
      rw [← div_pow, ← mul_pow, show ε / 6 * (6 / ε) = 1 by field_simp, one_pow]
    calc (1 + ε / 2) ^ ubP q ε = ε ^ (2 * q) / 6 ^ (2 * q) * ((6 / ε) ^ (2 * q) *
          (1 + ε / 2) ^ ubP q ε) := by rw [← mul_assoc, e, one_mul]
      _ ≤ νT * (1 + 3 * ε / 4) ^ ubP q ε := mul_le_mul hνTlow hRP' (by positivity) hνT0
  calc (1 + ε / 2) ^ ubP q ε ≤ νT * (1 + 3 * ε / 4) ^ ubP q ε := hfin
    _ = ∑ x, ν x * (ind T x * (1 + 3 * ε / 4) ^ ubP q ε) := by
        rw [hνT, sum_mul]; refine sum_congr rfl fun x _ => ?_; ring
    _ ≤ ∑ x, ν x * (f x + 1) ^ ubP q ε := by
        refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hν x)
        rw [ind_apply]
        split_ifs with hx
        · have : 3 * ε / 4 ≤ f x := by simpa [hT] using hx
          rw [one_mul]
          exact pow_le_pow_left₀ (by positivity) (by linarith) _
        · rw [zero_mul]; exact Even.pow_nonneg hPeven _

end

end KM

end KMFile_Unbalancing

section KMFile_Sifting



/-!
# Sifting (dependent random choice)

The dependent random choice lemma of Kelley–Meka in the form of Bloom–Sisask
(Lemmas 8, 9 of arXiv:2302.07211), relative to the measure `μ_{B₁} ○ μ_{B₂}`.
-/

open Finset

namespace KM

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The sifted set `B ∩ (A + s₁) ∩ ⋯ ∩ (A + s_p)`. -/
def sift (B A : Finset G) {p : ℕ} (s : Fin p → G) : Finset G :=
  B.filter fun b => ∀ j, b - s j ∈ A

lemma sift_subset (B A : Finset G) {p : ℕ} (s : Fin p → G) : sift B A s ⊆ B := filter_subset _ _

lemma sum_dconv_mu_mu_mul (B₁ B₂ : Finset G) (Φ : G → ℝ) :
    ∑ x, dconv (mu B₁) (mu B₂) x * Φ x =
      ((B₁.card : ℝ) * B₂.card)⁻¹ * ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂, Φ (b₁ - b₂) := by
  unfold dconv
  simp_rw [sum_mul]
  rw [sum_comm]
  have : ∀ y, ∑ x, mu B₁ (x + y) * mu B₂ y * Φ x = mu B₂ y * ∑ x, mu B₁ x * Φ (x - y) := by
    intro y
    rw [mul_sum, ← sum_sub_right _ y]
    refine sum_congr rfl fun x _ => ?_
    rw [sub_add_cancel]; ring
  simp_rw [this]
  rw [sum_mu_mul]
  simp_rw [sum_mu_mul]
  rw [sum_comm, mul_inv, mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  ring

lemma dconv_mu_self_sub (A : Finset G) (b₁ b₂ : G) :
    dconv (mu A) (mu A) (b₁ - b₂) =
      ((A.card : ℝ) ^ 2)⁻¹ * ∑ s, ind A (b₁ - s) * ind A (b₂ - s) := by
  unfold dconv
  rw [← sum_sub_left _ b₂, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [show b₁ - b₂ + (b₂ - s) = b₁ - s by abel]
  simp only [mu_eq_inv_mul_ind]
  ring

lemma prod_ind_sub (A : Finset G) {p : ℕ} (s : Fin p → G) (b : G) :
    ∏ j, ind A (b - s j) = if ∀ j, b - s j ∈ A then 1 else 0 := by
  unfold ind
  rw [prod_boole]
  simp

lemma dconv_mu_self_sub_pow (A : Finset G) (p : ℕ) (b₁ b₂ : G) :
    dconv (mu A) (mu A) (b₁ - b₂) ^ p =
      ((A.card : ℝ) ^ (2 * p))⁻¹ * ∑ s : Fin p → G,
        (if ∀ j, b₁ - s j ∈ A then 1 else 0) * (if ∀ j, b₂ - s j ∈ A then 1 else 0) := by
  rw [dconv_mu_self_sub, mul_pow, inv_pow, ← pow_mul]
  congr 1
  rw [← Fin.prod_const p, Fintype.prod_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [prod_mul_distrib, prod_ind_sub, prod_ind_sub]

/-- The key identity behind dependent random choice. -/
lemma sum_nu_pow_mul (A B₁ B₂ : Finset G) (p : ℕ) (f : G → ℝ) :
    ∑ x, dconv (mu B₁) (mu B₂) x * (dconv (mu A) (mu A) x ^ p * f x) =
      ((B₁.card : ℝ) * B₂.card * (A.card : ℝ) ^ (2 * p))⁻¹ *
        ∑ s : Fin p → G, ∑ b₁ ∈ sift B₁ A s, ∑ b₂ ∈ sift B₂ A s, f (b₁ - b₂) := by
  have hI : ∀ s : Fin p → G, ∑ b₁ ∈ sift B₁ A s, ∑ b₂ ∈ sift B₂ A s, f (b₁ - b₂) =
      ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂, (if ∀ j, b₁ - s j ∈ A then 1 else 0) *
        (if ∀ j, b₂ - s j ∈ A then 1 else 0) * f (b₁ - b₂) := by
    intro s
    simp only [sift, sum_filter]
    refine sum_congr rfl fun b₁ _ => ?_
    split_ifs <;> simp
  have hswap : ∀ g : (Fin p → G) → G → G → ℝ, ∑ s, ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂, g s b₁ b₂ =
      ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂, ∑ s, g s b₁ b₂ := by
    intro g; rw [sum_comm]; refine sum_congr rfl fun b₁ _ => ?_; rw [sum_comm]
  simp_rw [hI]
  rw [sum_dconv_mu_mu_mul, hswap]
  simp_rw [dconv_mu_self_sub_pow]
  simp only [mul_sum, sum_mul]
  refine sum_congr rfl fun b₁ _ => ?_
  refine sum_congr rfl fun b₂ _ => ?_
  refine sum_congr rfl fun s _ => ?_
  rw [mul_inv]
  ring

lemma card_sift_eq (B A : Finset G) {p : ℕ} (s : Fin p → G) :
    ((sift B A s).card : ℝ) = ∑ b ∈ B, ∏ j, ind A (b - s j) := by
  rw [sift, card_filter]
  push_cast
  refine sum_congr rfl fun b _ => ?_
  rw [prod_ind_sub]

lemma sum_card_sift (B A : Finset G) (p : ℕ) :
    ∑ s : Fin p → G, ((sift B A s).card : ℝ) = B.card * (A.card : ℝ) ^ p := by
  simp_rw [card_sift_eq]
  rw [sum_comm]
  have : ∀ b : G, ∑ s : Fin p → G, ∏ j, ind A (b - s j) = (A.card : ℝ) ^ p := by
    intro b
    rw [← Fintype.prod_sum (fun (_ : Fin p) t => ind A (b - t))]
    simp_rw [sum_sub_left (fun t => ind A t) b, sum_ind]
    simp
  simp_rw [this]
  rw [sum_const, nsmul_eq_mul]

lemma sum_card_mul_card_sift {A B₁ B₂ : Finset G} (hA : A.Nonempty) (hB₁ : B₁.Nonempty)
    (hB₂ : B₂.Nonempty) (p : ℕ) :
    ∑ s : Fin p → G, ((sift B₁ A s).card : ℝ) * (sift B₂ A s).card =
      (B₁.card : ℝ) * B₂.card * (A.card : ℝ) ^ (2 * p) *
        ∑ x, dconv (mu B₁) (mu B₂) x * dconv (mu A) (mu A) x ^ p := by
  have h := sum_nu_pow_mul A B₁ B₂ p (fun _ => 1)
  simp only [mul_one, sum_const, nsmul_eq_mul] at h
  rw [h, ← mul_assoc]
  have h0 : (B₁.card : ℝ) * B₂.card * (A.card : ℝ) ^ (2 * p) ≠ 0 := by
    have := hA.card_pos; have := hB₁.card_pos; have := hB₂.card_pos
    positivity
  rw [mul_inv_cancel₀ h0, one_mul]

/-- The abstract averaging argument behind dependent random choice. -/
lemma drc_abstract {ι : Type*} [Fintype ι] (a₁ a₂ I : ι → ℝ) (ha₁ : ∀ i, 0 ≤ a₁ i)
    (ha₂ : ∀ i, 0 ≤ a₂ i) (hI : ∀ i, 0 ≤ I i) (hQ : 0 < ∑ i, a₁ i * a₂ i) :
    ∃ i, (∑ i, a₁ i * a₂ i) ^ 2 / (4 * ((∑ i, a₁ i) * ∑ i, a₂ i)) ≤ a₁ i * a₂ i ∧
      I i ≤ 2 * ((∑ i, I i) / ∑ i, a₁ i * a₂ i) * (a₁ i * a₂ i) := by
  classical
  set Q := ∑ i, a₁ i * a₂ i with hQ_def
  set S₁ := ∑ i, a₁ i
  set S₂ := ∑ i, a₂ i
  have hS₁0 : 0 ≤ S₁ := sum_nonneg fun i _ => ha₁ i
  have hS : 0 < S₁ * S₂ := by
    have hQ'' : Q ≤ ∑ i, a₁ i * S₂ := by
      refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ha₁ i)
      exact single_le_sum (fun j _ => ha₂ j) (mem_univ i)
    have e : ∑ i, a₁ i * S₂ = S₁ * S₂ := by rw [← sum_mul]
    have hQ' : Q ≤ S₁ * S₂ := e ▸ hQ''
    have hS₁ : 0 ≤ S₁ := hS₁0
    have hS₂ : 0 ≤ S₂ := sum_nonneg fun i _ => ha₂ i
    rcases hS₁.lt_or_eq with h1 | h1
    · rcases hS₂.lt_or_eq with h2 | h2
      · positivity
      · rw [← h2, mul_zero] at hQ'; linarith
    · rw [← h1, zero_mul] at hQ'; linarith
  set M := Q / (2 * Real.sqrt (S₁ * S₂)) with hM_def
  have hsq : 0 < Real.sqrt (S₁ * S₂) := Real.sqrt_pos.2 hS
  have hM0 : 0 ≤ M := by positivity
  have hM2 : M ^ 2 = Q ^ 2 / (4 * (S₁ * S₂)) := by
    rw [hM_def, div_pow, mul_pow, Real.sq_sqrt hS.le]; norm_num
  set T := univ.filter fun i => a₁ i * a₂ i < M ^ 2
  have hT : ∑ i ∈ T, a₁ i * a₂ i ≤ Q / 2 := by
    calc ∑ i ∈ T, a₁ i * a₂ i ≤ ∑ i ∈ T, M * (Real.sqrt (a₁ i) * Real.sqrt (a₂ i)) := by
          refine sum_le_sum fun i hi => ?_
          rw [mem_filter] at hi
          have hw : 0 ≤ a₁ i * a₂ i := mul_nonneg (ha₁ i) (ha₂ i)
          rw [← Real.sqrt_mul (ha₁ i)]
          have h1 : Real.sqrt (a₁ i * a₂ i) ≤ M := by
            rw [Real.sqrt_le_left hM0]; exact hi.2.le
          calc a₁ i * a₂ i = Real.sqrt (a₁ i * a₂ i) * Real.sqrt (a₁ i * a₂ i) :=
                (Real.mul_self_sqrt hw).symm
            _ ≤ M * Real.sqrt (a₁ i * a₂ i) := by gcongr
      _ ≤ ∑ i, M * (Real.sqrt (a₁ i) * Real.sqrt (a₂ i)) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => by positivity)
      _ = M * ∑ i, Real.sqrt (a₁ i) * Real.sqrt (a₂ i) := by rw [mul_sum]
      _ ≤ M * (Real.sqrt S₁ * Real.sqrt S₂) := by
          gcongr; exact Real.sum_sqrt_mul_sqrt_le _ ha₁ ha₂
      _ = Q / 2 := by
          have e : Real.sqrt S₁ * Real.sqrt S₂ = Real.sqrt (S₁ * S₂) :=
            (Real.sqrt_mul hS₁0 _).symm
          rw [e, hM_def]
          field_simp
  have hTc : Q / 2 ≤ ∑ i ∈ univ.filter (fun i => ¬ a₁ i * a₂ i < M ^ 2), a₁ i * a₂ i := by
    have := sum_filter_add_sum_filter_not univ (fun i => a₁ i * a₂ i < M ^ 2)
      (fun i => a₁ i * a₂ i)
    linarith
  by_contra hcon
  push_neg at hcon
  set R := ∑ i, I i
  have hR0 : 0 ≤ R := sum_nonneg fun i _ => hI i
  have hne : (univ.filter (fun i => ¬ a₁ i * a₂ i < M ^ 2)).Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty] at he
    rw [he, sum_empty] at hTc
    linarith
  have key : 2 * (R / Q) * (Q / 2) < R := by
    calc 2 * (R / Q) * (Q / 2) ≤ 2 * (R / Q) *
          ∑ i ∈ univ.filter (fun i => ¬ a₁ i * a₂ i < M ^ 2), a₁ i * a₂ i := by
          gcongr
      _ = ∑ i ∈ univ.filter (fun i => ¬ a₁ i * a₂ i < M ^ 2),
          2 * (R / Q) * (a₁ i * a₂ i) := by rw [mul_sum]
      _ < ∑ i ∈ univ.filter (fun i => ¬ a₁ i * a₂ i < M ^ 2), I i := by
          refine sum_lt_sum_of_nonempty hne fun i hi => ?_
          rw [mem_filter] at hi
          have := hcon i (by rw [← hM2]; exact not_lt.1 hi.2)
          exact this
      _ ≤ R := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hI i)
  have : 2 * (R / Q) * (Q / 2) = R := by field_simp
  linarith

/-- **Sifting** (Kelley–Meka; Bloom–Sisask Lemma 8): if `μ_A ○ μ_A` has large `L^p(ν)` norm for
`ν = μ_{B₁} ○ μ_{B₂}`, then there are large `A₁ ⊆ B₁`, `A₂ ⊆ B₂` such that `μ_{A₁} ○ μ_{A₂}` is
concentrated where `μ_A ○ μ_A` is large. -/
theorem sifting {A B₁ B₂ : Finset G} (hA : A.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    {p : ℕ} {M ε δ : ℝ} (hM : 0 < M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 2 * (1 - ε) ^ p ≤ δ)
    (h : M ^ p ≤ ∑ x, dconv (mu B₁) (mu B₂) x * dconv (mu A) (mu A) x ^ p) :
    ∃ A₁ ⊆ B₁, ∃ A₂ ⊆ B₂, A₁.Nonempty ∧ A₂.Nonempty ∧
      ((A.card : ℝ) * M) ^ (2 * p) / 4 * B₁.card ≤ A₁.card ∧
      ((A.card : ℝ) * M) ^ (2 * p) / 4 * B₂.card ≤ A₂.card ∧
      1 - δ ≤ ∑ x, dconv (mu A₁) (mu A₂) x *
        ind (univ.filter fun x => (1 - ε) * M < dconv (mu A) (mu A) x) x := by
  set F := dconv (mu A) (mu A) with hF
  set ν := dconv (mu B₁) (mu B₂) with hν
  set T := univ.filter fun x => (1 - ε) * M < F x with hT
  let f : G → ℝ := fun x => 1 - ind T x
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [f]; linarith [ind_le_one T x]
  have hFnn : ∀ x, 0 ≤ F x := dconv_nonneg (mu_nonneg' A) (mu_nonneg' A)
  have hνnn : ∀ x, 0 ≤ ν x := dconv_nonneg (mu_nonneg' B₁) (mu_nonneg' B₂)
  have hνsum : ∑ x, ν x = 1 := by rw [hν, sum_dconv, sum_mu hB₁, sum_mu hB₂, one_mul]
  set P := ∑ x, ν x * F x ^ p with hP
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) h
  set c : ℝ := (B₁.card : ℝ) * B₂.card * (A.card : ℝ) ^ (2 * p) with hc
  have hc0 : 0 < c := by
    have := hA.card_pos; have := hB₁.card_pos; have := hB₂.card_pos
    positivity
  let a₁ : (Fin p → G) → ℝ := fun s => (sift B₁ A s).card
  let a₂ : (Fin p → G) → ℝ := fun s => (sift B₂ A s).card
  let I : (Fin p → G) → ℝ := fun s => ∑ b₁ ∈ sift B₁ A s, ∑ b₂ ∈ sift B₂ A s, f (b₁ - b₂)
  have hQ : ∑ s, a₁ s * a₂ s = c * P := sum_card_mul_card_sift hA hB₁ hB₂ p
  have hIsum : ∑ s, I s = c * ∑ x, ν x * (F x ^ p * f x) := by
    rw [sum_nu_pow_mul A B₁ B₂ p f, ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  have hIle : ∑ x, ν x * (F x ^ p * f x) ≤ (1 - ε) ^ p * P := by
    calc ∑ x, ν x * (F x ^ p * f x) ≤ ∑ x, ν x * ((1 - ε) * M) ^ p := by
          refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hνnn x)
          by_cases hx : x ∈ T
          · have : f x = 0 := by simp [f, hx]
            rw [this, mul_zero]; exact pow_nonneg (mul_nonneg (by linarith) hM.le) p
          · have : f x = 1 := by simp [f, hx]
            rw [this, mul_one]
            rw [hT, mem_filter] at hx
            push_neg at hx
            exact pow_le_pow_left₀ (hFnn x) (hx (mem_univ x)) p
      _ = ((1 - ε) * M) ^ p := by rw [← sum_mul, hνsum, one_mul]
      _ = (1 - ε) ^ p * M ^ p := mul_pow _ _ _
      _ ≤ (1 - ε) ^ p * P := mul_le_mul_of_nonneg_left h (pow_nonneg (by linarith) p)
  have hQpos : 0 < ∑ s, a₁ s * a₂ s := by rw [hQ]; positivity
  obtain ⟨s, hs1, hs2⟩ := drc_abstract a₁ a₂ I (fun s => Nat.cast_nonneg _)
    (fun s => Nat.cast_nonneg _) (fun s => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf0 _) hQpos
  have hS₁ : ∑ s, a₁ s = B₁.card * (A.card : ℝ) ^ p := sum_card_sift B₁ A p
  have hS₂ : ∑ s, a₂ s = B₂.card * (A.card : ℝ) ^ p := sum_card_sift B₂ A p
  rw [hS₁, hS₂, hQ] at hs1
  rw [hQ, hIsum] at hs2
  have hlow : (B₁.card : ℝ) * B₂.card * (((A.card : ℝ) * M) ^ (2 * p) / 4) ≤ a₁ s * a₂ s := by
    refine le_trans ?_ hs1
    have e : (c * P) ^ 2 / (4 * (B₁.card * (A.card : ℝ) ^ p * (B₂.card * (A.card : ℝ) ^ p))) =
        (B₁.card : ℝ) * B₂.card * ((A.card : ℝ) ^ (2 * p) * P ^ 2 / 4) := by
      have := hA.card_pos; have := hB₁.card_pos; have := hB₂.card_pos
      rw [hc]; field_simp; ring
    rw [e]
    gcongr
    rw [mul_pow, pow_mul' M, show (A.card : ℝ) ^ (2 * p) * (M ^ p) ^ 2 =
      (A.card : ℝ) ^ (2 * p) * (M ^ p) ^ 2 by ring]
    gcongr
  have ha₁le : a₁ s ≤ B₁.card := by
    show ((sift B₁ A s).card : ℝ) ≤ B₁.card; exact_mod_cast card_le_card (sift_subset B₁ A s)
  have ha₂le : a₂ s ≤ B₂.card := by
    show ((sift B₂ A s).card : ℝ) ≤ B₂.card; exact_mod_cast card_le_card (sift_subset B₂ A s)
  have ha₁0 : 0 ≤ a₁ s := Nat.cast_nonneg _
  have ha₂0 : 0 ≤ a₂ s := Nat.cast_nonneg _
  have hB₁0 : (0 : ℝ) < B₁.card := by exact_mod_cast hB₁.card_pos
  have hB₂0 : (0 : ℝ) < B₂.card := by exact_mod_cast hB₂.card_pos
  have hK0 : 0 < ((A.card : ℝ) * M) ^ (2 * p) / 4 := by
    have := hA.card_pos; positivity
  have hprod : 0 < a₁ s * a₂ s := lt_of_lt_of_le (by positivity) hlow
  have hne₁ : (sift B₁ A s).Nonempty := by
    have h1 : (0 : ℝ) < (sift B₁ A s).card := pos_of_mul_pos_left hprod ha₂0
    rw [← card_pos]; exact_mod_cast h1
  have hne₂ : (sift B₂ A s).Nonempty := by
    have h1 : (0 : ℝ) < (sift B₂ A s).card := pos_of_mul_pos_right hprod ha₁0
    rw [← card_pos]; exact_mod_cast h1
  refine ⟨sift B₁ A s, sift_subset _ _ _, sift B₂ A s, sift_subset _ _ _, hne₁, hne₂, ?_, ?_, ?_⟩
  · -- density of A₁
    by_contra hcon
    push_neg at hcon
    have : a₁ s * a₂ s < ((A.card : ℝ) * M) ^ (2 * p) / 4 * B₁.card * B₂.card := by
      calc a₁ s * a₂ s ≤ a₁ s * B₂.card := mul_le_mul_of_nonneg_left ha₂le ha₁0
        _ < ((A.card : ℝ) * M) ^ (2 * p) / 4 * B₁.card * B₂.card :=
          mul_lt_mul_of_pos_right hcon hB₂0
    linarith
  · by_contra hcon
    push_neg at hcon
    have : a₁ s * a₂ s < ((A.card : ℝ) * M) ^ (2 * p) / 4 * B₂.card * B₁.card := by
      calc a₁ s * a₂ s ≤ B₁.card * a₂ s := mul_le_mul_of_nonneg_right ha₁le ha₂0
        _ = a₂ s * B₁.card := mul_comm _ _
        _ < ((A.card : ℝ) * M) ^ (2 * p) / 4 * B₂.card * B₁.card :=
          mul_lt_mul_of_pos_right hcon hB₁0
    linarith
  · -- concentration
    have hsum1 : ∑ x, dconv (mu (sift B₁ A s)) (mu (sift B₂ A s)) x = 1 := by
      rw [sum_dconv, sum_mu hne₁, sum_mu hne₂, one_mul]
    have hIf : ∑ x, dconv (mu (sift B₁ A s)) (mu (sift B₂ A s)) x * f x =
        (a₁ s * a₂ s)⁻¹ * I s := by
      rw [sum_dconv_mu_mu_mul]
    have hIs : I s ≤ δ * (a₁ s * a₂ s) := by
      refine hs2.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hprod.le
      have : (c * ∑ x, ν x * (F x ^ p * f x)) / (c * P) ≤ (1 - ε) ^ p := by
        rw [div_le_iff₀ (by positivity)]
        calc c * ∑ x, ν x * (F x ^ p * f x) ≤ c * ((1 - ε) ^ p * P) := by gcongr
          _ = (1 - ε) ^ p * (c * P) := by ring
      linarith
    have hsplit : ∑ x, dconv (mu (sift B₁ A s)) (mu (sift B₂ A s)) x * ind T x =
        1 - ∑ x, dconv (mu (sift B₁ A s)) (mu (sift B₂ A s)) x * f x := by
      rw [← hsum1, ← sum_sub_distrib]
      refine sum_congr rfl fun x _ => ?_
      simp only [f]; ring
    rw [hsplit, hIf]
    have : (a₁ s * a₂ s)⁻¹ * I s ≤ δ := by
      rw [inv_mul_le_iff₀ hprod]; linarith
    linarith

end

end KM

end KMFile_Sifting

section KMFile_PosDef



/-!
# From a 3AP deficit to a large `L^P` norm of `μ_A ○ μ_A` against a sifting measure
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

/-- Jensen/Hölder: a large negative average on `C ⊆ X` gives a large `p`-th moment on `X`. -/
lemma moment_of_neg_avg {C X : Finset (ZMod N)} (hCX : C ⊆ X) (hC : C.Nonempty)
    {g : ZMod N → ℝ} {η : ℝ} (hη : 0 ≤ η) (h : ∑ x, mu C x * g x ≤ -η) {p : ℕ}
    (hp : Even p) :
    (C.card : ℝ) / X.card * η ^ p ≤ ∑ x, mu X x * g x ^ p := by
  have hCc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hXc : (0 : ℝ) < X.card := by exact_mod_cast (hC.mono hCX).card_pos
  have h1 : η ≤ ∑ x, mu C x * |g x| := by
    have : ∑ x, mu C x * (-g x) ≤ ∑ x, mu C x * |g x| :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (neg_le_abs _) (mu_nonneg C x)
    simp only [mul_neg, sum_neg_distrib] at this
    linarith
  have h2 : η ^ p ≤ ∑ x, mu C x * |g x| ^ p := by
    calc η ^ p ≤ (∑ x, mu C x * |g x|) ^ p := pow_le_pow_left₀ hη h1 p
      _ ≤ _ := Real.pow_arith_mean_le_arith_mean_pow univ _ _ (fun x _ => mu_nonneg C x)
          (sum_mu hC) (fun x _ => abs_nonneg _) p
  have h3 : ∀ x, mu C x * |g x| ^ p ≤ (X.card : ℝ) / C.card * (mu X x * g x ^ p) := by
    intro x
    rw [hp.pow_abs]
    have hg : 0 ≤ g x ^ p := hp.pow_nonneg _
    by_cases hx : x ∈ C
    · have hxX := hCX hx
      simp only [mu_apply, hx, hxX, if_true]
      have : (C.card : ℝ)⁻¹ = (X.card : ℝ) / C.card * (X.card : ℝ)⁻¹ := by field_simp
      rw [this]; ring_nf; exact le_rfl
    · simp only [mu_apply, hx, if_false, zero_mul]
      exact mul_nonneg (by positivity) (mul_nonneg (mu_nonneg X x) hg)
  have h4 : ∑ x, mu C x * |g x| ^ p ≤ (X.card : ℝ) / C.card * ∑ x, mu X x * g x ^ p := by
    rw [mul_sum]; exact sum_le_sum fun x _ => h3 x
  calc (C.card : ℝ) / X.card * η ^ p ≤ (C.card : ℝ) / X.card *
        ((X.card : ℝ) / C.card * ∑ x, mu X x * g x ^ p) := by
        gcongr; linarith
    _ = _ := by field_simp

lemma SuppIn.dconv {Γ : Finset (ZMod N)} {f g : ZMod N → ℝ} {r r' : ℝ} (hf : SuppIn f Γ r)
    (hg : SuppIn g Γ r') : SuppIn (KM.dconv f g) Γ (r + r') := by
  intro x hx
  obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero hx
  have h1 : f (x + y) ≠ 0 := left_ne_zero_of_mul hy
  have h2 : g y ≠ 0 := right_ne_zero_of_mul hy
  have := sub_mem_bohr (hf _ h1) (hg _ h2)
  simpa using this

/-- Positive-definiteness step: pass from `μ_X`-moments of `f * f` to `ν`-moments of `f ○ f`,
where `ν = h ○ h` is a probability measure supported on the `κ`-dilate of the regular `X`. -/
theorem posdef_bound {Γ : Finset (ZMod N)} {ρ κ ε : ℝ} (hreg : IsReg Γ ρ κ ε) (hρ : 0 ≤ ρ)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {h : ZMod N → ℝ} (hν0 : ∀ x, 0 ≤ KM.dconv h h x)
    (hν1 : ∑ x, KM.dconv h h x = 1) (hsupp : SuppIn (KM.dconv h h) Γ (κ * ρ))
    (f : ZMod N → ℝ) {p : ℕ} (hp : Even p) :
    ∑ x, mu (bohr Γ ρ) x * conv f f x ^ p ≤
      (1 + ε) * ∑ x, KM.dconv h h x * KM.dconv f f x ^ p := by
  set Bp := bohr Γ (ρ * (1 + κ))
  have hBp : Bp.Nonempty := bohr_nonempty (by nlinarith)
  have h1 : ∀ x, mu (bohr Γ ρ) x * conv f f x ^ p ≤
      (1 + ε) * (∑ t, mu Bp t * KM.dconv h h (x - t)) * conv f f x ^ p := by
    intro x
    have := hreg.mu_le_conv hρ hκ hε hν0 hν1 hsupp x
    rw [conv_comm, conv_apply] at this
    exact mul_le_mul_of_nonneg_right this (hp.pow_nonneg _)
  calc ∑ x, mu (bohr Γ ρ) x * conv f f x ^ p
      ≤ ∑ x, (1 + ε) * (∑ t, mu Bp t * KM.dconv h h (x - t)) * conv f f x ^ p :=
        sum_le_sum fun x _ => h1 x
    _ = (1 + ε) * ∑ t, mu Bp t * ∑ x, KM.dconv h h (x - t) * conv f f x ^ p := by
        rw [mul_sum]
        simp_rw [mul_sum, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun t _ => sum_congr rfl fun x _ => by ring
    _ ≤ (1 + ε) * ∑ t, mu Bp t * ∑ x, KM.dconv h h x * KM.dconv f f x ^ p := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left (sum_tr_dconv_mul_conv_pow_le f h p t) (mu_nonneg Bp t)
    _ = _ := by rw [← sum_mul, sum_mu hBp, one_mul]

lemma ubP_even (q : ℕ) (ε : ℝ) : Even (ubP q ε) := by
  unfold ubP; rw [mul_assoc]; exact even_two_mul _

lemma ceil_576 : ⌈36 / (1 / 4 : ℝ) ^ 2⌉₊ = 576 := by
  rw [show (36 / (1 / 4 : ℝ) ^ 2) = ((576 : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]

/-- Application of the unbalancing lemma: a large `p`-th moment of `F` gives a large `P`-th moment
of any nonnegative `g` which is `δ`-close to `F + 1` on the support of `ν`. -/
theorem unbal_apply {ν F g : ZMod N → ℝ} (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (hpos : ∀ k : ℕ, 0 ≤ ∑ x, ν x * F x ^ k) {p : ℕ} (hp : Even p) (hp4 : 4 ≤ p)
    (h1 : (1 / 4 : ℝ) ^ p ≤ ∑ x, ν x * F x ^ p) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 64)
    (hg0 : ∀ x, 0 ≤ g x) (hg : ∀ x, ν x ≠ 0 → |F x + 1 - g x| ≤ δ) :
    (17 / 16 : ℝ) ^ ubP (p + 1) (1 / 4) ≤ ∑ x, ν x * g x ^ ubP (p + 1) (1 / 4) := by
  set P := ubP (p + 1) (1 / 4) with hP
  have hq : Odd (p + 1) := hp.add_one
  have h2 : (1 / 4 : ℝ) ^ (p + 1) ≤ ∑ x, ν x * |F x| ^ (p + 1) := by
    refine lpow_mono hν0 hν1 (fun x => abs_nonneg _) (by omega) (Nat.le_succ p) (by norm_num) ?_
    simp_rw [hp.pow_abs]; exact h1
  have h3 := unbalancing hν0 hν1 hpos (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) hq
    (by omega) h2
  rw [← hP] at h3
  have hPe : Even P := ubP_even _ _
  have hPge : 38 ≤ P := by
    rw [hP, ubP]
    rw [ceil_576]
    omega
  -- pointwise bound
  have hpt : ∀ x, ν x * (F x + 1) ^ P ≤ ν x * ((1 + 2 * δ) ^ P * g x ^ P + 1) := by
    intro x
    by_cases hx : ν x = 0
    · simp [hx]
    refine mul_le_mul_of_nonneg_left ?_ (hν0 x)
    have hb := hg x hx
    have habs : |F x + 1| ≤ g x + δ := by
      have := abs_sub_abs_le_abs_sub (F x + 1) (g x)
      rw [abs_of_nonneg (hg0 x)] at this; linarith
    have e1 : (F x + 1) ^ P ≤ (g x + δ) ^ P := by
      rw [← hPe.pow_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs P
    refine e1.trans ?_
    by_cases hgx : 1 / 2 ≤ g x
    · have : g x + δ ≤ (1 + 2 * δ) * g x := by nlinarith
      calc (g x + δ) ^ P ≤ ((1 + 2 * δ) * g x) ^ P :=
            pow_le_pow_left₀ (by linarith [hg0 x]) this P
        _ = (1 + 2 * δ) ^ P * g x ^ P := mul_pow _ _ _
        _ ≤ _ := le_add_of_nonneg_right zero_le_one
    · push_neg at hgx
      have : (g x + δ) ^ P ≤ 1 := pow_le_one₀ (by linarith [hg0 x]) (by linarith)
      have : 0 ≤ (1 + 2 * δ) ^ P * g x ^ P := mul_nonneg (by positivity) (pow_nonneg (hg0 x) _)
      linarith
  have h4 : ∑ x, ν x * (F x + 1) ^ P ≤ (1 + 2 * δ) ^ P * ∑ x, ν x * g x ^ P + 1 := by
    calc ∑ x, ν x * (F x + 1) ^ P ≤ ∑ x, ν x * ((1 + 2 * δ) ^ P * g x ^ P + 1) :=
          sum_le_sum fun x _ => hpt x
      _ = _ := by
        simp_rw [mul_add, mul_one, sum_add_distrib, hν1, mul_sum]
        congr 1; refine sum_congr rfl fun x _ => by ring
  -- numerics
  have hbern : (2 : ℝ) ≤ (576 / 561 : ℝ) ^ P := by
    have := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 15 / 561) P
    have hP' : (38 : ℝ) ≤ P := by exact_mod_cast hPge
    calc (2 : ℝ) ≤ 1 + P * (15 / 561) := by nlinarith
      _ ≤ (1 + 15 / 561) ^ P := this
      _ = _ := by norm_num
  have ha1 : (1 : ℝ) ≤ (561 / 512 : ℝ) ^ P := one_le_pow₀ (by norm_num)
  have hkey : (561 / 512 : ℝ) ^ P ≤ (9 / 8 : ℝ) ^ P - 1 := by
    have : (9 / 8 : ℝ) ^ P = (561 / 512 : ℝ) ^ P * (576 / 561 : ℝ) ^ P := by
      rw [← mul_pow]; norm_num
    nlinarith
  have h98 : (1 + 1 / 4 / 2 : ℝ) = 9 / 8 := by norm_num
  rw [h98] at h3
  have hδ' : (17 / 16 : ℝ) * (1 + 2 * δ) ≤ 561 / 512 := by nlinarith
  have hc : (17 / 16 : ℝ) ^ P * (1 + 2 * δ) ^ P ≤ (561 / 512 : ℝ) ^ P := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hδ' P
  have hpos' : (0 : ℝ) < (1 + 2 * δ) ^ P := by positivity
  have : (17 / 16 : ℝ) ^ P * (1 + 2 * δ) ^ P ≤ (1 + 2 * δ) ^ P * ∑ x, ν x * g x ^ P := by
    linarith
  rw [mul_comm] at this
  exact le_of_mul_le_mul_left this hpos'

/-- Decomposition of `h ○ h` for `h = f₁ * f₂` as an average of `f₁ ○ (translate of f₂)`. -/
lemma dconv_conv_self_eq (f₁ f₂ : ZMod N → ℝ) (x : ZMod N) :
    KM.dconv (conv f₁ f₂) (conv f₁ f₂) x =
      ∑ t, KM.dconv f₁ f₂ t * KM.dconv f₁ (fun y => f₂ (y - t)) x := by
  simp only [dconv_apply, conv_apply]
  simp_rw [sum_mul, mul_sum]
  have key : ∀ F : ZMod N → ZMod N → ZMod N → ℝ,
      ∑ a, ∑ b, ∑ c, F a b c = ∑ p : ZMod N × ZMod N × ZMod N, F p.1 p.2.1 p.2.2 := by
    intro F; simp only [Fintype.sum_prod_type]
  rw [key (fun y b c => f₁ b * f₂ (x + y - b) * (f₁ c * f₂ (y - c))),
    key (fun t u w => f₁ (t + u) * f₂ u * (f₁ (x + w) * f₂ (w - t)))]
  let e : ZMod N × ZMod N × ZMod N ≃ ZMod N × ZMod N × ZMod N :=
    { toFun := fun p => (p.2.1 + p.2.2, x + p.2.2, p.1 + p.2.1)
      invFun := fun q => (q.2.2 - q.1 + q.2.1 - x, q.1 - q.2.1 + x, q.2.1 - x)
      left_inv := fun p => by ext <;> simp <;> ring
      right_inv := fun q => by ext <;> simp <;> ring }
  symm
  refine Fintype.sum_equiv e _ _ (fun p => ?_)
  obtain ⟨t, u, w⟩ := p
  simp only [e, Equiv.coe_fn_mk]
  rw [show x + (u + w) - (x + w) = u by ring, show u + w - (t + u) = w - t by ring]
  ring

/-- Translating a normalised indicator. -/
lemma mu_sub_eq (S : Finset (ZMod N)) (x t : ZMod N) :
    mu S (x - t) = mu (S.image (· + t)) x := by
  rw [mu_eq_inv_mul_ind, mu_eq_inv_mul_ind]
  simp only
  rw [ind_sub_eq, card_image_of_injective _ (add_left_injective t)]

/-- Averaging: some term of a convex combination is at least the average. -/
lemma exists_ge_of_avg {ι : Type*} [Fintype ι] {w V : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {c : ℝ} (h : c ≤ ∑ i, w i * V i) : ∃ i, c ≤ V i := by
  by_contra hcon
  push_neg at hcon
  have hne : ∃ i, 0 < w i := by
    by_contra h'; push_neg at h'
    have : ∑ i, w i ≤ 0 := sum_nonpos fun i _ => h' i
    linarith
  obtain ⟨i₀, hi₀⟩ := hne
  have : ∑ i, w i * V i < ∑ i, w i * c :=
    sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hcon i).le (hw i))
      ⟨i₀, mem_univ _, mul_lt_mul_of_pos_left (hcon i₀) hi₀⟩
  rw [← sum_mul, hw1, one_mul] at this
  linarith

end

end KM

end KMFile_PosDef

section KMFile_StepUnbal



/-!
# The unbalancing step of the density increment

From a dense 3AP-trivial set `A₁` in a regular Bohr set `B₁` (with a dense part `A₂` in a
narrower Bohr set) we get a large `L^P` norm of `μ_{A₁} ○ μ_{A₁}` against a positive definite
measure `h ○ h`.
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

theorem step_unbal {Γ Γ' : Finset (ZMod N)} (hΓ' : ∀ r, bohr Γ' r ⊆ bohr Γ (2 * r))
    {ρ₁ ρ₂ κ ε₁ ε₂ : ℝ} (hρ₁ : 0 < ρ₁) (hκ : 0 ≤ κ) (hε₁ : 0 ≤ ε₁)
    (hreg₁ : IsReg Γ ρ₁ κ ε₁) (hρ₂ : 0 < ρ₂) (hρ₂₁ : 2 * ρ₂ ≤ κ * ρ₁) (hκ1 : κ ≤ 1)
    (hε₂ : 0 ≤ ε₂) (hε₂1 : ε₂ ≤ 1) (hreg₂ : IsReg Γ' ρ₂ κ ε₂)
    (hcardX : (bohr Γ' ρ₂).card = (bohr Γ ρ₂).card)
    (hinj : ∀ b b' : ZMod N, b + b = b' + b' → b = b')
    (hdouble : ∀ b ∈ bohr Γ ρ₂, b + b ∈ bohr Γ' ρ₂)
    {A₁ A₂ : Finset (ZMod N)} (hA₁ : A₁ ⊆ bohr Γ ρ₁) (hT : Tri A₁) (hA₂A₁ : A₂ ⊆ A₁)
    (hA₂ : A₂ ⊆ bohr Γ ρ₂) {α₁ : ℝ} (hα₁ : 0 < α₁)
    (hA₁c : α₁ * (bohr Γ ρ₁).card ≤ A₁.card) (hA₂c : α₁ * (bohr Γ ρ₂).card ≤ A₂.card)
    (hB : 4 ≤ α₁ ^ 2 * (bohr Γ ρ₁).card) (hε₁α : 128 * ε₁ ≤ α₁)
    {h : ZMod N → ℝ} (hν0 : ∀ x, 0 ≤ dconv h h x) (hν1 : ∑ x, dconv h h x = 1)
    (hsupp : SuppIn (dconv h h) Γ' (κ * ρ₂))
    {p : ℕ} (hp : Even p) (hp4 : 4 ≤ p) (hαp : 2 ≤ α₁ * 2 ^ p) :
    ((17 / 16 : ℝ) / (bohr Γ ρ₁).card) ^ ubP (p + 1) (1 / 4) ≤
      ∑ x, dconv h h x * dconv (mu A₁) (mu A₁) x ^ ubP (p + 1) (1 / 4) := by
  set B₁ := bohr Γ ρ₁ with hB₁
  set B₂ := bohr Γ ρ₂ with hB₂
  set X := bohr Γ' ρ₂ with hX
  set ν := dconv h h with hν
  have hB₁c : (0 : ℝ) < B₁.card := by exact_mod_cast bohr_card_pos hρ₁.le
  have hB₂c : (0 : ℝ) < B₂.card := by exact_mod_cast bohr_card_pos hρ₂.le
  have hA₂c' : (0 : ℝ) < A₂.card := lt_of_lt_of_le (by positivity) hA₂c
  have hA₂ne : A₂.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hA₂c'
  set C := A₂.image fun b => b + b with hC
  have hCX : C ⊆ X := by
    intro y hy
    rw [hC, mem_image] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact hdouble b (hA₂ hb)
  have hCne : C.Nonempty := hA₂ne.image _
  have hCcard : C.card = A₂.card := card_image_of_injective _ (fun b b' h => hinj b b' h)
  -- count bound
  have hA₂B : ∀ b ∈ A₂, b + b ∈ bohr Γ (κ * ρ₁) := by
    intro b hb
    exact bohr_mono (by linarith) (add_mem_bohr (hA₂ hb) (hA₂ hb))
  have hcount := count_bound hreg₁ hρ₁.le hκ hε₁ hA₁ hT hA₂A₁ hA₂ne hA₂B hα₁ hA₁c hB
    (by linarith)
  set f : ZMod N → ℝ := fun x => mu A₁ x - mu B₁ x with hf
  have hmom := moment_of_neg_avg hCX hCne (g := conv f f)
    (η := 1 / (2 * (B₁.card : ℝ))) (by positivity) hcount hp
  have hpd := posdef_bound hreg₂ hρ₂.le hκ hε₂ hν0 hν1 hsupp f hp
  have hCX' : α₁ ≤ (C.card : ℝ) / X.card := by
    rw [hCcard, hX, hcardX, le_div_iff₀ hB₂c]; exact hA₂c
  -- the p-th moment of `F = |B₁| (f ○ f)`
  set F : ZMod N → ℝ := fun x => (B₁.card : ℝ) * dconv f f x with hF
  have hFp : ∀ k : ℕ, ∑ x, ν x * F x ^ k = (B₁.card : ℝ) ^ k * ∑ x, ν x * dconv f f x ^ k := by
    intro k; rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; rw [hF]; ring
  have hpos : ∀ k : ℕ, 0 ≤ ∑ x, ν x * F x ^ k := by
    intro k; rw [hFp]
    exact mul_nonneg (by positivity) (sum_dconv_mul_dconv_pow_nonneg f h k)
  have h1 : (1 / 4 : ℝ) ^ p ≤ ∑ x, ν x * F x ^ p := by
    rw [hFp]
    have e1 : α₁ * (1 / (2 * (B₁.card : ℝ))) ^ p ≤ (1 + ε₂) * ∑ x, ν x * dconv f f x ^ p := by
      calc α₁ * (1 / (2 * (B₁.card : ℝ))) ^ p ≤ (C.card : ℝ) / X.card *
            (1 / (2 * (B₁.card : ℝ))) ^ p := by gcongr
        _ ≤ _ := hmom.trans hpd
    have e2 : (1 / (2 * (B₁.card : ℝ))) ^ p = (1 / 2) ^ p * ((B₁.card : ℝ) ^ p)⁻¹ := by
      field_simp
      rw [← mul_pow]; congr 1; field_simp
    rw [e2] at e1
    have hBp : (0 : ℝ) < (B₁.card : ℝ) ^ p := by positivity
    have e3 : α₁ * (1 / 2) ^ p ≤ (1 + ε₂) * ((B₁.card : ℝ) ^ p * ∑ x, ν x * dconv f f x ^ p) := by
      have := mul_le_mul_of_nonneg_left e1 hBp.le
      have ee : (B₁.card : ℝ) ^ p * (α₁ * ((1 / 2) ^ p * ((B₁.card : ℝ) ^ p)⁻¹)) =
          α₁ * (1 / 2) ^ p := by field_simp
      rw [ee] at this; linarith
    have e4 : (1 + ε₂) * (1 / 4 : ℝ) ^ p ≤ α₁ * (1 / 2) ^ p := by
      have : (1 / 4 : ℝ) ^ p = (1 / 2) ^ p * (1 / 2) ^ p := by
        rw [← mul_pow]; norm_num
      rw [this]
      have h2p : (1 / 2 : ℝ) ^ p * 2 ^ p = 1 := by rw [← mul_pow]; norm_num
      have hh : 0 < (1 / 2 : ℝ) ^ p := by positivity
      calc (1 + ε₂) * ((1 / 2 : ℝ) ^ p * (1 / 2) ^ p) ≤ 2 * ((1 / 2 : ℝ) ^ p * (1 / 2) ^ p) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (α₁ * 2 ^ p) * ((1 / 2 : ℝ) ^ p * (1 / 2) ^ p) :=
            mul_le_mul_of_nonneg_right hαp (by positivity)
        _ = α₁ * (1 / 2) ^ p := by linear_combination (α₁ * (1 / 2 : ℝ) ^ p) * h2p
    have hpos' : (0 : ℝ) < 1 + ε₂ := by linarith
    exact le_of_mul_le_mul_left (e4.trans e3) hpos'
  -- the final unbalancing
  set g : ZMod N → ℝ := fun x => (B₁.card : ℝ) * dconv (mu A₁) (mu A₁) x with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    mul_nonneg hB₁c.le (dconv_nonneg (mu_nonneg' _) (mu_nonneg' _) x)
  have hA₁ne : A₁.Nonempty := hA₂ne.mono hA₂A₁
  have hgF : ∀ x, ν x ≠ 0 → |F x + 1 - g x| ≤ 2 * ε₁ / α₁ := by
    intro x hx
    have hx1 : x ∈ bohr Γ' (κ * ρ₂) := hsupp x hx
    have hx2 : x ∈ bohr Γ (κ * ρ₁) := by
      refine bohr_mono ?_ (hΓ' _ hx1)
      nlinarith
    exact dconv_error_bound hreg₁ hρ₁.le hκ hε₁ hA₁ hA₁ne hα₁ hA₁c hx2
  have hδ0 : 0 ≤ 2 * ε₁ / α₁ := by positivity
  have hδ : 2 * ε₁ / α₁ ≤ 1 / 64 := by
    rw [div_le_iff₀ hα₁]; linarith
  have hfin := unbal_apply hν0 hν1 hpos hp hp4 h1 hδ0 hδ hg0 hgF
  generalize ubP (p + 1) (1 / 4) = P at hfin ⊢
  have e5 : ∑ x, ν x * g x ^ P = (B₁.card : ℝ) ^ P * ∑ x, ν x * dconv (mu A₁) (mu A₁) x ^ P := by
    rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; rw [hg]; ring
  rw [e5] at hfin
  rw [div_pow, div_le_iff₀ (pow_pos hB₁c P)]
  linarith [mul_comm ((B₁.card : ℝ) ^ P) (∑ x, ν x * dconv (mu A₁) (mu A₁) x ^ P)]

end

end KM

end KMFile_StepUnbal

section KMFile_StepFinal



/-!
# Sifting plus almost periodicity: the final step of the density increment
-/

open Finset
open scoped Pointwise

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma exists_translate_of_dconv_conv {X₁ X₂ : Finset (ZMod N)} (hX₁ : X₁.Nonempty)
    (hX₂ : X₂.Nonempty) {Φ : ZMod N → ℝ} {c : ℝ}
    (h : c ≤ ∑ x, dconv (conv (mu X₁) (mu X₂)) (conv (mu X₁) (mu X₂)) x * Φ x) :
    ∃ t, c ≤ ∑ x, dconv (mu X₁) (mu (X₂.image (· + t))) x * Φ x := by
  have e : ∑ x, dconv (conv (mu X₁) (mu X₂)) (conv (mu X₁) (mu X₂)) x * Φ x =
      ∑ t, dconv (mu X₁) (mu X₂) t * ∑ x, dconv (mu X₁) (mu (X₂.image (· + t))) x * Φ x := by
    simp_rw [dconv_conv_self_eq, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => sum_congr rfl fun x _ => ?_
    have : (fun y => mu X₂ (y - t)) = mu (X₂.image (· + t)) := by
      funext y; exact mu_sub_eq X₂ y t
    rw [this, mul_assoc]
  rw [e] at h
  refine exists_ge_of_avg (fun t => dconv_nonneg (mu_nonneg' _) (mu_nonneg' _) t) ?_ h
  rw [sum_dconv, sum_mu hX₁, sum_mu hX₂, one_mul]

lemma conv_mu_bohr_eq_relDens (A : Finset (ZMod N)) (Γ : Finset (ZMod N)) (ρ : ℝ) (x : ZMod N) :
    conv (mu A) (mu (bohr Γ ρ)) x = relDens A (bohr Γ ρ) x / A.card := by
  rw [conv_mu_bohr_eq_dconv, dconv_mu_mu_apply, relDens]
  simp only [div_eq_mul_inv, mul_inv]
  ring

lemma exists_of_dconv_mu_ne_zero {A B : Finset (ZMod N)} {x : ZMod N}
    (h : dconv (mu A) (mu B) x ≠ 0) : ∃ a ∈ A, ∃ b ∈ B, x = a - b := by
  obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero h
  have h1 : mu A (x + y) ≠ 0 := left_ne_zero_of_mul hy
  have h2 : mu B y ≠ 0 := right_ne_zero_of_mul hy
  have hA : x + y ∈ A := by by_contra hc; exact h1 (by simp [mu_apply, hc])
  have hB : y ∈ B := by by_contra hc; exact h2 (by simp [mu_apply, hc])
  exact ⟨x + y, hA, y, hB, by ring⟩

lemma pow_99_le {P : ℕ} (hP : 800 ≤ P) : 2 * (1 - 1 / 100 : ℝ) ^ P ≤ 1 / 100 := by
  have h1 : (1 - 1 / 100 : ℝ) ^ 100 ≤ 1 / 2 := by norm_num
  have h2 : (1 - 1 / 100 : ℝ) ^ P ≤ (1 - 1 / 100) ^ 800 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hP
  have h3 : (1 - 1 / 100 : ℝ) ^ 800 ≤ (1 / 2) ^ 8 := by
    rw [show 800 = 100 * 8 from rfl, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) h1 8
  have h4 : (1 / 2 : ℝ) ^ 8 = 1 / 256 := by norm_num
  have h5 := h2.trans (h3.trans_eq h4)
  calc 2 * (1 - 1 / 100 : ℝ) ^ P ≤ 2 * (1 / 256) := by gcongr
    _ ≤ 1 / 100 := by norm_num

theorem step_final {Γ' : Finset (ZMod N)} {A₁ : Finset (ZMod N)} (hA₁ : A₁.Nonempty)
    {Bc α₁ : ℝ} (hBc : 0 < Bc) (hα₁ : 0 < α₁) (hA₁c : α₁ * Bc ≤ A₁.card)
    {P r k Lc : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r) (hP : 800 ≤ P)
    (hrP : 8 ≤ (4 : ℝ) ^ r * α₁ ^ (2 * P))
    (hL : 8 * Real.log (8 * ((4 : ℝ) ^ r) ^ csM r (1 / 100 / 4 / (2 * k))) < Lc)
    {ρX₁ ρX₂ ρY ρ₀ κX κ₀ εX₁ εX₂ εY ε₀ : ℝ} (hρX₁ : 0 < ρX₁) (hρX₂ : 0 < ρX₂) (hρY : 0 < ρY)
    (hρ₀ : 0 < ρ₀) (hκX : 0 ≤ κX) (hκ₀ : 0 ≤ κ₀) (hεX₁ : 0 ≤ εX₁) (hεX₂ : 0 ≤ εX₂)
    (hεY : 0 ≤ εY) (hε₀ : 0 ≤ ε₀) (hεX₁1 : εX₁ ≤ 1) (hεX₂1 : εX₂ ≤ 1) (hεY1 : εY ≤ 1)
    (hregX₁ : IsReg Γ' ρX₁ κX εX₁) (hX₂sub : ρX₂ ≤ κX * ρX₁)
    (hregX₂ : IsReg Γ' ρX₂ κX εX₂) (hYsub : ρY ≤ κX * ρX₂)
    (hregY : IsReg Γ' ρY κX εY) (hreg₀ : IsReg Γ' ρ₀ κ₀ ε₀) (hLρ : Lc * ρ₀ ≤ κX * ρY)
    {ν₀ : ℝ} (hν₀ : ν₀ + 2 * (1 / 2) ^ k ≤ α₁ / 400)
    (hsum : ((17 / 16) / Bc) ^ P ≤ ∑ x, dconv (conv (mu (bohr Γ' ρX₁)) (mu (bohr Γ' ρX₂)))
      (conv (mu (bohr Γ' ρX₁)) (mu (bohr Γ' ρX₂))) x * dconv (mu A₁) (mu A₁) x ^ P) :
    ∃ Δ : Finset (ZMod N), Δ.card ≤ Lc ∧ ∀ ρ₃ : ℝ, 0 ≤ ρ₃ → ρ₃ ≤ κ₀ * ρ₀ →
      6 * ε₀ + Lc * (2 * Real.pi * ρ₃) ≤ ν₀ →
        ∃ x, (1033 / 1000) * (A₁.card / Bc) ≤ relDens A₁ (bohr (Γ' ∪ Δ) ρ₃) x := by
  set X₁ := bohr Γ' ρX₁ with hX₁
  set X₂ := bohr Γ' ρX₂ with hX₂
  set Y := bohr Γ' ρY with hY
  set M : ℝ := (17 / 16) / Bc with hM
  have hMpos : 0 < M := by positivity
  have hX₁ne : X₁.Nonempty := bohr_nonempty hρX₁.le
  have hX₂ne : X₂.Nonempty := bohr_nonempty hρX₂.le
  have hA₁c' : (0 : ℝ) < A₁.card := by exact_mod_cast hA₁.card_pos
  -- choose the translate
  obtain ⟨t, ht⟩ := exists_translate_of_dconv_conv hX₁ne hX₂ne hsum
  set X₂t := X₂.image (· + t) with hX₂t
  have hX₂tne : X₂t.Nonempty := hX₂ne.image _
  have hX₂tc : X₂t.card = X₂.card := card_image_of_injective _ (add_left_injective t)
  -- sifting
  obtain ⟨A₁', hA₁'X, A₂', hA₂'X, hA₁'ne, hA₂'ne, hA₁'c, hA₂'c, hcorr⟩ :=
    sifting hA₁ hX₁ne hX₂tne hMpos (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num)
      (pow_99_le hP) ht
  set τ : ℝ := ((A₁.card : ℝ) * M) ^ (2 * P) / 4 with hτ
  have hAM : α₁ ≤ (A₁.card : ℝ) * M := by
    rw [hM]
    have : α₁ * Bc * (17 / 16 / Bc) = α₁ * (17 / 16) := by field_simp
    have h2 : α₁ * Bc * (17 / 16 / Bc) ≤ (A₁.card : ℝ) * (17 / 16 / Bc) :=
      mul_le_mul_of_nonneg_right hA₁c (by positivity)
    linarith
  have hτpos : 0 < τ := by
    rw [hτ]; have : 0 < (A₁.card : ℝ) * M := by positivity
    positivity
  have hτ4 : 2 ≤ (4 : ℝ) ^ r * τ := by
    have h1 : α₁ ^ (2 * P) ≤ ((A₁.card : ℝ) * M) ^ (2 * P) :=
      pow_le_pow_left₀ hα₁.le hAM _
    have h4 : (0 : ℝ) ≤ 4 ^ r := by positivity
    have h5 := mul_le_mul_of_nonneg_left h1 h4
    have e : (4 : ℝ) ^ r * (((A₁.card : ℝ) * M) ^ (2 * P) / 4) =
        (4 ^ r * ((A₁.card : ℝ) * M) ^ (2 * P)) / 4 := by ring
    rw [hτ, e]
    linarith
  have hX₁A : (X₁.card : ℝ) ≤ (A₁'.card : ℝ) / τ := by
    rw [le_div_iff₀ hτpos]; linarith
  have hX₂A : (X₂.card : ℝ) ≤ (A₂'.card : ℝ) / τ := by
    rw [le_div_iff₀ hτpos, ← hX₂tc]; linarith
  have hA₁'c' : (0 : ℝ) < A₁'.card := by exact_mod_cast hA₁'ne.card_pos
  have hA₂'c' : (0 : ℝ) < A₂'.card := by exact_mod_cast hA₂'ne.card_pos
  -- the restricted set
  set S := univ.filter fun x => (1 - 1 / 100) * M < dconv (mu A₁) (mu A₁) x with hS
  set S' := S ∩ (X₁ + X₂).image (· - t) with hS'
  have hsupp : ∀ x, dconv (mu A₁') (mu A₂') x ≠ 0 → x ∈ (X₁ + X₂).image (· - t) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_of_dconv_mu_ne_zero hx
    have hb' := hA₂'X hb
    rw [hX₂t, mem_image] at hb'
    obtain ⟨c, hc, rfl⟩ := hb'
    rw [mem_image]
    refine ⟨a + -c, Finset.add_mem_add (hA₁'X ha) (neg_mem_bohr hc), by ring⟩
  have hcorr' : 1 - 1 / 100 ≤ ∑ x, dconv (mu A₁') (mu A₂') x * ind S' x := by
    refine hcorr.trans (le_of_eq (sum_congr rfl fun x _ => ?_))
    by_cases hx : dconv (mu A₁') (mu A₂') x = 0
    · simp [hx]
    · have := hsupp x hx
      congr 1
      simp only [ind_apply, hS', mem_inter, this, and_true]
  have hX₁X₂ : ((X₁ + X₂).card : ℝ) ≤ 2 * X₁.card := by
    have := hregX₁.card_add_le hρX₁.le hκX hεX₁ (bohr_mono hX₂sub)
    calc ((X₁ + X₂).card : ℝ) ≤ (1 + εX₁) * X₁.card := this
      _ ≤ 2 * X₁.card := by gcongr; linarith
  have hS'c : (S'.card : ℝ) ≤ 4 ^ r * A₁'.card := by
    have h1 : S'.card ≤ ((X₁ + X₂).image (· - t)).card := card_le_card inter_subset_right
    have h2 : ((X₁ + X₂).image (· - t)).card ≤ (X₁ + X₂).card := card_image_le
    have h3 : (S'.card : ℝ) ≤ (X₁ + X₂).card := by exact_mod_cast h1.trans h2
    have h5 : 2 * (A₁'.card : ℝ) / τ ≤ 4 ^ r * A₁'.card := by
      rw [div_le_iff₀ hτpos]
      have := mul_le_mul_of_nonneg_right hτ4 hA₁'c'.le
      linarith
    have h6 : 2 * (X₁.card : ℝ) ≤ 2 * (A₁'.card : ℝ) / τ := by
      rw [mul_div_assoc]; linarith
    linarith
  have hK : ((A₂' + Y).card : ℝ) ≤ 4 ^ r * A₂'.card := by
    have hsub : A₂' + Y ⊆ (X₂ + Y).image (· + t) := by
      intro z hz
      obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hz
      have ha' := hA₂'X ha
      rw [hX₂t, mem_image] at ha'
      obtain ⟨c, hc, rfl⟩ := ha'
      rw [mem_image]
      exact ⟨c + y, Finset.add_mem_add hc hy, by ring⟩
    have h1 : ((A₂' + Y).card : ℝ) ≤ (X₂ + Y).card := by
      exact_mod_cast (card_le_card hsub).trans card_image_le
    have h2 := hregX₂.card_add_le hρX₂.le hκX hεX₂ (bohr_mono hYsub)
    have h5 : 2 * (A₂'.card : ℝ) / τ ≤ 4 ^ r * A₂'.card := by
      rw [div_le_iff₀ hτpos]
      have := mul_le_mul_of_nonneg_right hτ4 hA₂'c'.le
      linarith
    have h6 : 2 * (X₂.card : ℝ) ≤ 2 * (A₂'.card : ℝ) / τ := by
      rw [mul_div_assoc]; linarith
    have h7 : (1 + εX₂) * (X₂.card : ℝ) ≤ 2 * X₂.card := by gcongr; linarith
    linarith
  -- apply the generic increment
  set M' : ℝ := (1 - 1 / 100) * M / (1 + 2 * (1 / 100)) with hM'
  have hM'pos : 0 < M' := by positivity
  have h2 : ∀ x ∈ S', (1 + 2 * (1 / 100 : ℝ)) * M' ≤ dconv (mu A₁) (mu A₁) x := by
    intro x hx
    have hx' : x ∈ S := mem_of_mem_inter_left hx
    rw [hS, mem_filter] at hx'
    rw [hM', mul_div_cancel₀ _ (by norm_num)]
    exact hx'.2.le
  have hν₀' : (ν₀ + 2 * (1 / 2) ^ k) / A₁.card ≤ (1 / 100) * M' / 4 := by
    rw [div_le_iff₀ hA₁c']
    have e1 : (1 / 100) * M' / 4 * A₁.card ≥ (1 / 100) * M' / 4 * (α₁ * Bc) :=
      mul_le_mul_of_nonneg_left hA₁c (by positivity)
    have e2 : (1 / 100) * M' / 4 * (α₁ * Bc) = α₁ * (1 / 400) * (99 / 100 * (17 / 16) / (102 / 100)) := by
      rw [hM', hM]; field_simp; ring
    linarith
  obtain ⟨Δ, hΔ, hfin⟩ := gen_increment hA₁ hA₁'ne hA₂'ne (by norm_num : (0 : ℝ) < 1 / 100)
    (by norm_num) hM'pos hcorr' h2 hρY hκX hεY hεY1 hregY hK hr hS'c hk hρ₀ hκ₀ hε₀ hreg₀ hLρ
    hL hν₀'
  refine ⟨Δ, hΔ, fun ρ₃ hρ₃ hρ₃' hρ₃'' => ?_⟩
  obtain ⟨x, hx⟩ := hfin ρ₃ hρ₃ hρ₃' hρ₃''
  refine ⟨x, ?_⟩
  rw [conv_mu_bohr_eq_relDens, le_div_iff₀ hA₁c'] at hx
  have e3 : (1 + 1 / 100 / 4) * M' * A₁.card = (401 / 400) * (99 / 100) * (17 / 16) / (102 / 100) *
      (A₁.card / Bc) := by
    rw [hM', hM]; field_simp; norm_num
  rw [e3] at hx
  have hq : (0 : ℝ) ≤ A₁.card / Bc := by positivity
  linarith

end

end KM

end KMFile_StepFinal

section KMFile_Params



/-!
# The numerical parameters of the density increment iteration

Everything depends only on a natural number `ℓ ≥ 1` with `2^{-ℓ} ≤ α`.
-/

open Finset

namespace KM

noncomputable section

def kP (ℓ : ℕ) : ℕ := ℓ + 11
def pP (ℓ : ℕ) : ℕ := 2 * ℓ + 4
def PP (ℓ : ℕ) : ℕ := ubP (pP ℓ + 1) (1 / 4)
def rP (ℓ : ℕ) : ℕ := PP ℓ * (ℓ + 1) + 2
def csP (ℓ : ℕ) : ℕ := csM (rP ℓ) (1 / 100 / 4 / (2 * ((kP ℓ : ℕ) : ℝ)))
def LcP (ℓ : ℕ) : ℕ := 8 * (3 + 2 * rP ℓ * csP ℓ)
def DmP (ℓ : ℕ) : ℕ := 100 * ℓ * LcP ℓ
def aP (ℓ : ℕ) : ℝ := (1 / 2) ^ ℓ
def κP (ℓ : ℕ) : ℝ := aP ℓ / (6400 * (DmP ℓ + 1))
def FP (ℓ : ℕ) : ℝ := κP ℓ ^ 7 / (409600 * LcP ℓ)

lemma PP_eq (ℓ : ℕ) : PP ℓ = 1152 * (2 * ℓ + 5) := by
  rw [PP, ubP, ceil_576, pP]; ring

lemma PP_ge (ℓ : ℕ) : 800 ≤ PP ℓ := by rw [PP_eq]; omega

lemma csP_eq (ℓ : ℕ) : csP ℓ = 20480000 * rP ℓ ^ 2 * kP ℓ ^ 2 := by
  rw [csP, csM]
  have hk : (0 : ℝ) < kP ℓ := by rw [kP]; positivity
  rw [show 32 * ((rP ℓ : ℕ) : ℝ) ^ 2 / (1 / 100 / 4 / (2 * ((kP ℓ : ℕ) : ℝ))) ^ 2 =
    ((20480000 * rP ℓ ^ 2 * kP ℓ ^ 2 : ℕ) : ℝ) by push_cast; field_simp; ring, Nat.ceil_natCast]

lemma LcP_pos (ℓ : ℕ) : 24 ≤ LcP ℓ := by rw [LcP]; omega

lemma aP_pos (ℓ : ℕ) : 0 < aP ℓ := by rw [aP]; positivity

lemma aP_le (ℓ : ℕ) : aP ℓ ≤ 1 := by rw [aP]; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma κP_pos (ℓ : ℕ) : 0 < κP ℓ := by
  rw [κP]; have := aP_pos ℓ; positivity

lemma κP_le_a (ℓ : ℕ) : κP ℓ ≤ aP ℓ / 6400 := by
  rw [κP]
  have := aP_pos ℓ
  apply div_le_div_of_nonneg_left this.le (by norm_num)
  have : (0 : ℝ) ≤ DmP ℓ := by positivity
  nlinarith

lemma κP_le (ℓ : ℕ) : κP ℓ ≤ 1 / 8 := by
  have := κP_le_a ℓ; have := aP_le ℓ; linarith

lemma κP_reg (ℓ : ℕ) {d : ℕ} (hd : d ≤ DmP ℓ) : 32 * κP ℓ * d ≤ aP ℓ / 200 := by
  rw [κP]
  have ha := aP_pos ℓ
  have hd' : (d : ℝ) ≤ DmP ℓ := by exact_mod_cast hd
  have hD : (0 : ℝ) < 6400 * ((DmP ℓ : ℝ) + 1) := by positivity
  rw [mul_comm 32, mul_assoc, div_mul_eq_mul_div, div_le_div_iff₀ hD (by norm_num)]
  nlinarith

lemma κP_reg1 (ℓ : ℕ) {d : ℕ} (hd : d ≤ DmP ℓ) : 32 * κP ℓ * d ≤ 1 := by
  have := κP_reg ℓ hd; have := aP_le ℓ; linarith

lemma κP_reg0 (ℓ : ℕ) {d : ℕ} (hd : d ≤ DmP ℓ) : 0 ≤ 32 * κP ℓ * d := by
  have := κP_pos ℓ; positivity

lemma hrP_fact (ℓ : ℕ) {α₁ : ℝ} (hα : (1 / 2) ^ (ℓ + 1) ≤ α₁) :
    8 ≤ (4 : ℝ) ^ rP ℓ * α₁ ^ (2 * PP ℓ) := by
  have h1 : ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ (2 * PP ℓ) ≤ α₁ ^ (2 * PP ℓ) :=
    pow_le_pow_left₀ (by positivity) hα _
  have h2 : (4 : ℝ) ^ rP ℓ * ((1 / 2 : ℝ) ^ (ℓ + 1)) ^ (2 * PP ℓ) = 16 := by
    rw [rP, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [show 2 * (PP ℓ * (ℓ + 1) + 2) = (ℓ + 1) * (2 * PP ℓ) + 4 by ring, pow_add, one_div,
      inv_pow]
    have : (2 : ℝ) ^ ((ℓ + 1) * (2 * PP ℓ)) ≠ 0 := by positivity
    field_simp; norm_num
  have h3 : (0 : ℝ) ≤ 4 ^ rP ℓ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h3]

lemma hL_fact (ℓ : ℕ) :
    8 * Real.log (8 * ((4 : ℝ) ^ rP ℓ) ^ csM (rP ℓ) (1 / 100 / 4 / (2 * ((kP ℓ : ℕ) : ℝ)))) <
      LcP ℓ := by
  rw [← csP]
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
  have h8 : Real.log 8 < 3 := by
    have := Real.log_two_lt_d9
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; linarith
  have h4 : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have h40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hcr : (0 : ℝ) ≤ (csP ℓ : ℝ) * rP ℓ := by positivity
  rw [LcP]; push_cast
  nlinarith

lemma FP_pos (ℓ : ℕ) : 0 < FP ℓ := by
  rw [FP]; have := κP_pos ℓ; have : (0 : ℝ) < LcP ℓ := by have := LcP_pos ℓ; positivity
  positivity

end

end KM

end KMFile_Params

section KMFile_Increment



/-!
# The density increment lemma
-/

open Finset
open scoped Pointwise

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma two_mul_inv_two (hN : Odd N) : (2 : ZMod N) * (2 : ZMod N)⁻¹ = 1 := by
  have := ZMod.coe_mul_inv_eq_one (n := N) 2 (Nat.coprime_two_left.mpr hN)
  simpa using this

lemma bohr_half_subset (hN : Odd N) (Γ : Finset (ZMod N)) (r : ℝ) :
    bohr (Γ.image (· * (2 : ZMod N)⁻¹)) r ⊆ bohr Γ (2 * r) := by
  intro x hx
  rw [mem_bohr] at hx ⊢
  intro γ hγ
  have h1 := hx (γ * (2 : ZMod N)⁻¹) (mem_image_of_mem _ hγ)
  have h2 : γ * x = ((2 : ℕ) : ZMod N) * (γ * (2 : ZMod N)⁻¹ * x) := by
    push_cast
    linear_combination (γ * x) * (two_mul_inv_two hN).symm
  rw [h2]
  refine (cn_natCast_mul_le 2 _).trans ?_
  push_cast; linarith

lemma double_mem_bohr_half (hN : Odd N) {Γ : Finset (ZMod N)} {r : ℝ} {b : ZMod N}
    (hb : b ∈ bohr Γ r) : b + b ∈ bohr (Γ.image (· * (2 : ZMod N)⁻¹)) r := by
  rw [mem_bohr] at hb ⊢
  intro γ' hγ'
  rw [mem_image] at hγ'
  obtain ⟨γ, hγ, rfl⟩ := hγ'
  have : γ * (2 : ZMod N)⁻¹ * (b + b) = γ * b := by
    linear_combination (γ * b) * (two_mul_inv_two hN)
  rw [this]; exact hb γ hγ

lemma double_inj (hN : Odd N) {b b' : ZMod N} (h : b + b = b' + b') : b = b' := by
  have h2 : (2 : ZMod N)⁻¹ * (b + b) = (2 : ZMod N)⁻¹ * (b' + b') := by rw [h]
  have e : ∀ c : ZMod N, (2 : ZMod N)⁻¹ * (c + c) = c := fun c => by
    linear_combination c * (two_mul_inv_two hN)
  rw [e, e] at h2; exact h2

lemma chain_lower {κ Lc ρ₂ ρX₁ ρX₂ ρY ρ₀ ρ₃ : ℝ} (hκ : 0 ≤ κ) (hLc : 0 < Lc)
    (h1 : κ * ρ₂ / 8 / 2 ≤ ρX₁) (h2 : κ * ρX₁ / 2 ≤ ρX₂) (h3 : κ * ρX₂ / 2 ≤ ρY)
    (h4 : κ * ρY / Lc / 2 ≤ ρ₀) (h5 : κ / 100 * ρ₀ / 2 ≤ ρ₃) :
    κ ^ 5 * ρ₂ / (25600 * Lc) ≤ ρ₃ := by
  have e1 : κ ^ 5 * ρ₂ / (25600 * Lc) =
      κ / 100 * (κ * (κ * (κ * (κ * ρ₂ / 8 / 2) / 2) / 2) / Lc / 2) / 2 := by
    field_simp; ring
  rw [e1]
  refine le_trans ?_ h5
  gcongr
  refine le_trans ?_ h4
  gcongr
  refine le_trans ?_ h3
  gcongr
  refine le_trans ?_ h2
  gcongr

set_option maxHeartbeats 1000000 in
theorem increment_main (hN : Odd N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {Γ : Finset (ZMod N)}
    (hΓ : Γ.card + LcP ℓ ≤ DmP ℓ) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ ≤ 1)
    (hreg₁ : IsReg Γ ρ₁ (κP ℓ) (32 * κP ℓ * Γ.card)) (hρ₂ : 0 < ρ₂)
    (hρ₂₁ : ρ₂ ≤ κP ℓ * ρ₁ / 2) (hreg₂ : IsReg Γ ρ₂ (κP ℓ) (32 * κP ℓ * Γ.card))
    {A₁ A₂ : Finset (ZMod N)} (hA₁ : A₁ ⊆ bohr Γ ρ₁) (hT : Tri A₁) (hA₂A₁ : A₂ ⊆ A₁)
    (hA₂ : A₂ ⊆ bohr Γ ρ₂) {α₁ : ℝ} (hα₁ : 49 / 50 * aP ℓ ≤ α₁)
    (hA₁c : α₁ * (bohr Γ ρ₁).card ≤ A₁.card) (hA₂c : α₁ * (bohr Γ ρ₂).card ≤ A₂.card)
    (hB : 4 ≤ α₁ ^ 2 * (bohr Γ ρ₁).card) :
    ∃ Γ'' : Finset (ZMod N), ∃ ρ₃ : ℝ, Γ''.card ≤ Γ.card + LcP ℓ ∧
      κP ℓ ^ 5 * ρ₂ / (25600 * LcP ℓ) ≤ ρ₃ ∧ 0 < ρ₃ ∧ ρ₃ ≤ ρ₂ ∧
      IsReg Γ'' ρ₃ (κP ℓ) (32 * κP ℓ * Γ''.card) ∧
      ∃ x, 1033 / 1000 * (A₁.card / (bohr Γ ρ₁).card) ≤ relDens A₁ (bohr Γ'' ρ₃) x := by
  set κ := κP ℓ with hκdef
  set a := aP ℓ with hadef
  set Lc := LcP ℓ with hLcdef
  have ha := aP_pos ℓ
  have ha1 := aP_le ℓ
  have hκ := κP_pos ℓ
  have hκ8 := κP_le ℓ
  have hκa := κP_le_a ℓ
  have hLc : (24 : ℝ) ≤ Lc := by exact_mod_cast LcP_pos ℓ
  have hα₁pos : 0 < α₁ := by linarith
  set d := Γ.card with hd
  have hdD : d ≤ DmP ℓ := by omega
  set Γ' := Γ.image (· * (2 : ZMod N)⁻¹) with hΓ'def
  have hd' : Γ'.card ≤ DmP ℓ := card_image_le.trans hdD
  have hε := κP_reg ℓ hdD
  have hε' := κP_reg ℓ hd'
  have hε'0 := κP_reg0 ℓ hd'
  have hε0 := κP_reg0 ℓ hdD
  have hε'1 := κP_reg1 ℓ hd'
  -- the halved Bohr sets
  have hΓ' : ∀ r, bohr Γ' r ⊆ bohr Γ (2 * r) := bohr_half_subset hN Γ
  have hcardX : (bohr Γ' ρ₂).card = (bohr Γ ρ₂).card :=
    card_bohr_image_mul Γ (two_mul_inv_two hN) ρ₂
  have hregX : IsReg Γ' ρ₂ κ (32 * κ * d) := (isReg_image_mul_iff Γ (two_mul_inv_two hN)).mpr hreg₂
  -- radii
  have hκ0 : 0 < κ / 100 := by positivity
  have hk1 : κ ≤ 1 := by linarith
  have kmul : ∀ x : ℝ, 0 ≤ x → κ * x ≤ x := fun x hx => mul_le_of_le_one_left hx hk1
  have e100 : 32 * (κ / 100) * (Γ'.card : ℝ) = 32 * κ * Γ'.card / 100 := by ring
  obtain ⟨ρX₁, hX₁l, hX₁u, hregX₁⟩ := exists_reg Γ' (by positivity : 0 < κ * ρ₂ / 8) hκ hκ8 hε'1
  have hρX₁ : 0 < ρX₁ := by
    have : 0 < κ * ρ₂ / 8 / 2 := by positivity
    linarith
  obtain ⟨ρX₂, hX₂l, hX₂u, hregX₂⟩ := exists_reg Γ' (by positivity : 0 < κ * ρX₁) hκ hκ8 hε'1
  have hρX₂ : 0 < ρX₂ := by
    have : 0 < κ * ρX₁ / 2 := by positivity
    linarith
  obtain ⟨ρY, hYl, hYu, hregY⟩ := exists_reg Γ' (by positivity : 0 < κ * ρX₂) hκ hκ8 hε'1
  have hρY : 0 < ρY := by
    have : 0 < κ * ρX₂ / 2 := by positivity
    linarith
  have hLcpos : (0 : ℝ) < Lc := by linarith
  obtain ⟨ρ₀, h₀l, h₀u, hreg₀⟩ := exists_reg Γ' (by positivity : 0 < κ * ρY / Lc) hκ0
    (by linarith) (by rw [e100]; linarith)
  have hρ₀ : 0 < ρ₀ := by
    have : 0 < κ * ρY / Lc / 2 := by positivity
    linarith
  -- chain of inequalities between radii
  have hρ₂1 : ρ₂ ≤ 1 := by have := kmul ρ₁ hρ₁.le; linarith
  have hX₁1 : ρX₁ ≤ ρ₂ := by have := kmul ρ₂ hρ₂.le; linarith
  have hX₂1 : ρX₂ ≤ ρX₁ := by have := kmul ρX₁ hρX₁.le; linarith
  have hY1 : ρY ≤ ρX₂ := by have := kmul ρX₂ hρX₂.le; linarith
  have hρY1 : ρY ≤ 1 := by linarith
  -- the positive definite measure
  set X₁ := bohr Γ' ρX₁ with hX₁
  set X₂ := bohr Γ' ρX₂ with hX₂
  set h := conv (mu X₁) (mu X₂) with hh
  have hX₁ne : X₁.Nonempty := bohr_nonempty hρX₁.le
  have hX₂ne : X₂.Nonempty := bohr_nonempty hρX₂.le
  have hh0 : 0 ≤ h := conv_nonneg (mu_nonneg' _) (mu_nonneg' _)
  have hν0 : ∀ x, 0 ≤ dconv h h x := fun x => dconv_nonneg hh0 hh0 x
  have hν1 : ∑ x, dconv h h x = 1 := by
    rw [sum_dconv, hh, sum_conv, sum_mu hX₁ne, sum_mu hX₂ne]; norm_num
  have hsupp : SuppIn (dconv h h) Γ' (κ * ρ₂) := by
    have h1 : SuppIn h Γ' (ρX₁ + ρX₂) := SuppIn.conv suppIn_mu suppIn_mu
    have h2 := SuppIn.dconv h1 h1
    exact h2.mono (by linarith)
  -- unbalancing
  have hp2 : 2 ≤ α₁ * 2 ^ pP ℓ := by
    have e : a * 2 ^ pP ℓ = 2 ^ (ℓ + 4) := by
      rw [hadef, aP, pP, show 2 * ℓ + 4 = ℓ + (ℓ + 4) by ring, pow_add, ← mul_assoc, ← mul_pow]
      norm_num
    have e2 : (2 : ℝ) ^ (ℓ + 4) ≥ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
    have e3 : (0 : ℝ) ≤ 2 ^ pP ℓ := by positivity
    have e4 := mul_le_mul_of_nonneg_right hα₁ e3
    have e5 : 49 / 50 * a * 2 ^ pP ℓ = 49 / 50 * (a * 2 ^ pP ℓ) := by ring
    rw [e5, e] at e4
    linarith
  have hsum := step_unbal hΓ' hρ₁ hκ.le hε0 hreg₁ hρ₂ (by linarith) (by linarith) hε0
    (by linarith) hregX hcardX (fun b b' hb => double_inj hN hb)
    (fun b hb => double_mem_bohr_half hN hb) hA₁ hT hA₂A₁ hA₂ hα₁pos hA₁c hA₂c hB
    (by linarith) hν0 hν1 hsupp (p := pP ℓ) (by rw [pP]; exact ⟨ℓ + 2, by ring⟩)
    (by rw [pP]; omega) hp2
  -- final step
  have hA₂ne : A₂.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < A₂.card :=
      lt_of_lt_of_le (mul_pos hα₁pos (by exact_mod_cast bohr_card_pos hρ₂.le)) hA₂c
    exact_mod_cast this
  have hA₁ne : A₁.Nonempty := hA₂ne.mono hA₂A₁
  have hBc : (0 : ℝ) < (bohr Γ ρ₁).card := by exact_mod_cast bohr_card_pos hρ₁.le
  have hαl : (1 / 2 : ℝ) ^ (ℓ + 1) ≤ α₁ := by
    rw [pow_succ]; change a * (1 / 2) ≤ α₁ at *; linarith
  have hν₀ : a / 1000 + 2 * (1 / 2) ^ kP ℓ ≤ α₁ / 400 := by
    have : (1 / 2 : ℝ) ^ kP ℓ = a / 2048 := by
      rw [kP, pow_add, hadef, aP]; ring
    rw [this]; linarith
  obtain ⟨Δ, hΔ, hfin⟩ := step_final hA₁ne hBc hα₁pos hA₁c (P := PP ℓ) (r := rP ℓ) (k := kP ℓ)
    (Lc := Lc) (by rw [kP]; omega) (by rw [rP]; omega) (PP_ge ℓ) (hrP_fact ℓ hαl) (hL_fact ℓ)
    hρX₁ hρX₂ hρY hρ₀ hκ.le hκ0.le hε'0 hε'0 hε'0 (by positivity) (by linarith) (by linarith)
    (by linarith) hregX₁ hX₂u hregX₂ hYu hregY hreg₀
    (by rw [le_div_iff₀ hLcpos] at h₀u; linarith) hν₀ hsum
  -- the new Bohr set
  set Γ'' := Γ' ∪ Δ with hΓ''
  have hΓ''c : Γ''.card ≤ d + Lc := by
    have h1 : Γ''.card ≤ Γ'.card + Δ.card := card_union_le Γ' Δ
    have h2 : Γ'.card ≤ d := card_image_le
    omega
  have hΓ''D : Γ''.card ≤ DmP ℓ := by omega
  obtain ⟨ρ₃, h₃l, h₃u, hreg₃⟩ := exists_reg Γ'' (by positivity : 0 < κ / 100 * ρ₀) hκ hκ8
    (κP_reg1 ℓ hΓ''D)
  have hρ₃ : 0 < ρ₃ := by
    have : 0 < κ / 100 * ρ₀ / 2 := by positivity
    linarith
  have hcond : 6 * (32 * (κ / 100) * Γ'.card) + Lc * (2 * Real.pi * ρ₃) ≤ a / 1000 := by
    have e1 : 32 * (κ / 100) * Γ'.card ≤ a / 20000 := by
      rw [e100]; linarith
    have e2 : Lc * ρ₃ ≤ κ / 100 * κ := by
      have i1 : Lc * ρ₀ ≤ κ * ρY := by rw [le_div_iff₀ hLcpos] at h₀u; linarith
      have i2 : Lc * ρ₃ ≤ Lc * (κ / 100 * ρ₀) := mul_le_mul_of_nonneg_left h₃u hLcpos.le
      have i3 : κ * ρY ≤ κ := mul_le_of_le_one_right hκ.le hρY1
      have i4 : Lc * (κ / 100 * ρ₀) = κ / 100 * (Lc * ρ₀) := by ring
      have i5 : κ / 100 * (Lc * ρ₀) ≤ κ / 100 * κ :=
        mul_le_mul_of_nonneg_left (i1.trans i3) hκ0.le
      linarith
    have e3 : κ / 100 * κ ≤ a / 640000 := by
      have := kmul κ hκ.le
      have e : κ / 100 * κ = κ * κ / 100 := by ring
      rw [e]; linarith
    have e4 : Lc * (2 * Real.pi * ρ₃) ≤ 8 * (Lc * ρ₃) := by
      have := Real.pi_lt_four
      have i0 : 0 ≤ Lc * ρ₃ := by positivity
      have i1 : Lc * (2 * Real.pi * ρ₃) = (2 * Real.pi) * (Lc * ρ₃) := by ring
      rw [i1]
      exact mul_le_mul_of_nonneg_right (by linarith only [this]) i0
    linarith only [e1, e2, e3, e4, ha]
  obtain ⟨x, hx⟩ := hfin ρ₃ hρ₃.le h₃u hcond
  refine ⟨Γ'', ρ₃, hΓ''c, ?_, hρ₃, ?_, hreg₃, x, hx⟩
  · exact chain_lower hκ.le hLcpos hX₁l hX₂l hYl h₀l h₃l
  · have i1 : κ / 100 * ρ₀ ≤ ρ₀ := mul_le_of_le_one_left hρ₀.le (by linarith only [hk1])
    have i2 : ρ₀ ≤ ρY := by
      rw [le_div_iff₀ hLcpos] at h₀u
      have i3 := kmul ρY hρY.le
      have i4 : ρ₀ ≤ ρ₀ * Lc := le_mul_of_one_le_right hρ₀.le (by linarith only [hLc])
      linarith only [i3, i4, h₀u]
    linarith only [i1, i2, h₃u, hY1, hX₂1, hX₁1]

end

end KM

end KMFile_Increment

section KMFile_IncrementFull



/-!
# The density increment lemma (full form, including Bourgain's narrowing)
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The translated part of `A` lying in `x₀ + B₁`. -/
def transl (A B₁ : Finset (ZMod N)) (x₀ : ZMod N) : Finset (ZMod N) :=
  (A.filter fun a => a - x₀ ∈ B₁).image (· - x₀)

lemma transl_subset (A B₁ : Finset (ZMod N)) (x₀ : ZMod N) : transl A B₁ x₀ ⊆ B₁ := by
  intro y hy
  rw [transl, mem_image] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  exact (mem_filter.mp ha).2

lemma card_transl (A B₁ : Finset (ZMod N)) (x₀ : ZMod N) :
    ((transl A B₁ x₀).card : ℝ) = relDens A B₁ x₀ * B₁.card := by
  rw [transl, card_image_of_injective _ (sub_left_injective), relDens]
  by_cases h : (B₁.card : ℝ) = 0
  · have : B₁ = ∅ := by exact_mod_cast Finset.card_eq_zero.mp (by exact_mod_cast h)
    subst this; simp
  · field_simp

lemma transl_mono (A : Finset (ZMod N)) {B B' : Finset (ZMod N)} (h : B ⊆ B') (x₀ : ZMod N) :
    transl A B x₀ ⊆ transl A B' x₀ := by
  apply image_subset_image
  intro a ha
  rw [mem_filter] at ha ⊢
  exact ⟨ha.1, h ha.2⟩

lemma Tri.transl {A : Finset (ZMod N)} (hT : Tri A) (B₁ : Finset (ZMod N)) (x₀ : ZMod N) :
    Tri (transl A B₁ x₀) :=
  (hT.mono (filter_subset _ _)).image_sub x₀

lemma relDens_transl_le (A B₁ B : Finset (ZMod N)) (x₀ x : ZMod N) :
    relDens (transl A B₁ x₀) B x ≤ relDens A B (x + x₀) := by
  unfold relDens
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : (transl A B₁ x₀).filter (fun a => a - x ∈ B) ⊆
      (A.filter fun a => a - (x + x₀) ∈ B).image (· - x₀) := by
    intro y hy
    rw [mem_filter, transl, mem_image] at hy
    obtain ⟨⟨a, ha, rfl⟩, hb⟩ := hy
    rw [mem_image]
    refine ⟨a, mem_filter.mpr ⟨(mem_filter.mp ha).1, ?_⟩, rfl⟩
    have : a - (x + x₀) = a - x₀ - x := by ring
    rw [this]; exact hb
  exact_mod_cast (card_le_card hsub).trans card_image_le

lemma FP_le (ℓ : ℕ) : FP ℓ ≤ κP ℓ ^ 2 / 8 := by
  have hκ := κP_pos ℓ
  have hκ1 : κP ℓ ≤ 1 := by have := κP_le ℓ; linarith
  have hLc : (24 : ℝ) ≤ LcP ℓ := by exact_mod_cast LcP_pos ℓ
  rw [FP, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h5 : κP ℓ ^ 7 ≤ κP ℓ ^ 2 := pow_le_pow_of_le_one hκ.le hκ1 (by norm_num)
  have h2 : 0 ≤ κP ℓ ^ 2 := by positivity
  nlinarith

lemma chain_upper {κ Lc ρ ρ₁ ρ₂ ρ₃ : ℝ} (hκ : 0 ≤ κ) (hLc : 0 < Lc) (hρ : 0 ≤ ρ)
    (h1 : κ * ρ / 2 ≤ ρ₁) (h2 : κ * ρ₁ / 2 / 2 ≤ ρ₂) (h3 : κ ^ 5 * ρ₂ / (25600 * Lc) ≤ ρ₃) :
    κ ^ 7 / (409600 * Lc) * ρ ≤ ρ₃ := by
  refine le_trans ?_ h3
  have e : κ ^ 7 / (409600 * Lc) * ρ = κ ^ 5 * (κ * (κ * ρ / 2) / 2 / 2) / (25600 * Lc) / 2 := by
    field_simp; ring
  rw [e]
  have h4 : κ ^ 5 * (κ * (κ * ρ / 2) / 2 / 2) / (25600 * Lc) ≤ κ ^ 5 * ρ₂ / (25600 * Lc) := by
    gcongr
    refine le_trans ?_ h2
    gcongr
  have h5 : 0 ≤ κ ^ 5 * (κ * (κ * ρ / 2) / 2 / 2) / (25600 * Lc) := by positivity
  linarith

set_option maxHeartbeats 1000000 in
/-- **The density increment lemma.** A dense 3AP-trivial subset of a regular Bohr set either
forces the Bohr set to be small, or has an increased density on a translate of a new regular Bohr
set of slightly larger rank and not much smaller radius. -/
theorem increment (hN : Odd N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {Γ : Finset (ZMod N)}
    (hΓ : Γ.card + LcP ℓ ≤ DmP ℓ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hreg : IsReg Γ ρ (κP ℓ) (32 * κP ℓ * Γ.card))
    {A : Finset (ZMod N)} (hA : A ⊆ bohr Γ ρ) (hT : Tri A) {α : ℝ} (hαa : aP ℓ ≤ α)
    (hAc : α * (bohr Γ ρ).card ≤ A.card) :
    (N : ℝ) * (κP ℓ * ρ / 4) ^ Γ.card < 4 / (49 / 50 * aP ℓ) ^ 2 ∨
    ∃ Γ' : Finset (ZMod N), ∃ ρ' : ℝ, Γ'.card ≤ Γ.card + LcP ℓ ∧ FP ℓ * ρ ≤ ρ' ∧ 0 < ρ' ∧
      ρ' ≤ 1 / 2 ∧ IsReg Γ' ρ' (κP ℓ) (32 * κP ℓ * Γ'.card) ∧
      ∃ x, (101 / 100) * α ≤ relDens A (bohr Γ' ρ') x := by
  set κ := κP ℓ with hκdef
  set a := aP ℓ with hadef
  set d := Γ.card with hd
  have ha := aP_pos ℓ
  have hκ := κP_pos ℓ
  have hκ8 := κP_le ℓ
  have hk1 : κ ≤ 1 := by linarith
  have hdD : d ≤ DmP ℓ := by omega
  have hε := κP_reg ℓ hdD
  have hε0 := κP_reg0 ℓ hdD
  have hε1 := κP_reg1 ℓ hdD
  have hFP := FP_le ℓ
  have hFP0 := FP_pos ℓ
  obtain ⟨ρ₁, h₁l, h₁u, hreg₁⟩ := exists_reg Γ (by positivity : 0 < κ * ρ) hκ hκ8 hε1
  have hρ₁ : 0 < ρ₁ := by have : 0 < κ * ρ / 2 := by positivity
                          linarith
  obtain ⟨ρ₂, h₂l, h₂u, hreg₂⟩ := exists_reg Γ (by positivity : 0 < κ * ρ₁ / 2) hκ hκ8 hε1
  have hρ₂ : 0 < ρ₂ := by have : 0 < κ * ρ₁ / 2 / 2 := by positivity
                          linarith
  have hκρ : κ * ρ ≤ ρ := mul_le_of_le_one_left hρ.le hk1
  have hκρ₁ : κ * ρ₁ ≤ ρ₁ := mul_le_of_le_one_left hρ₁.le hk1
  have hρ₁ρ : ρ₁ ≤ ρ := h₁u.trans hκρ
  have hρ₂ρ₁ : ρ₂ ≤ ρ₁ := by linarith
  have hsub₂ : ρ₂ ≤ κ * ρ := by
    have : κ * ρ₁ ≤ κ * (κ * ρ) := mul_le_mul_of_nonneg_left h₁u hκ.le
    have : κ * (κ * ρ) ≤ κ * ρ := mul_le_of_le_one_left (by positivity) hk1
    linarith
  have hθ : 2 * (32 * κ * d) ≤ 1 / 100 * α := by linarith
  rcases bour hreg hρ hκ.le hε0 hA hAc (bohr_nonempty hρ₁.le) (bohr_nonempty hρ₂.le)
    (bohr_mono h₁u) (bohr_mono hsub₂) hθ with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x₀, hx₁, hx₂⟩
  · right
    refine ⟨Γ, ρ₁, by omega, ?_, hρ₁, by linarith, hreg₁, x, by linarith⟩
    have : FP ℓ ≤ κ / 2 := by
      have : κ ^ 2 ≤ κ := by nlinarith
      linarith
    have : FP ℓ * ρ ≤ κ / 2 * ρ := mul_le_mul_of_nonneg_right this hρ.le
    linarith
  · right
    refine ⟨Γ, ρ₂, by omega, ?_, hρ₂, by linarith, hreg₂, x, by linarith⟩
    have i1 : FP ℓ * ρ ≤ κ ^ 2 / 8 * ρ := mul_le_mul_of_nonneg_right hFP hρ.le
    have i2 : κ * (κ * ρ / 2) ≤ κ * ρ₁ := mul_le_mul_of_nonneg_left h₁l hκ.le
    have i3 : κ ^ 2 / 8 * ρ = κ * (κ * ρ / 2) / 4 := by ring
    linarith
  · set B₁ := bohr Γ ρ₁ with hB₁
    set B₂ := bohr Γ ρ₂ with hB₂
    set A₁ := transl A B₁ x₀ with hA₁
    set A₂ := transl A B₂ x₀ with hA₂
    have hB₁c : (0 : ℝ) < B₁.card := by exact_mod_cast bohr_card_pos hρ₁.le
    have hB₂c : (0 : ℝ) < B₂.card := by exact_mod_cast bohr_card_pos hρ₂.le
    set α₁ := 49 / 50 * α with hα₁
    have hA₁c : α₁ * B₁.card ≤ A₁.card := by
      rw [hA₁, card_transl]
      exact mul_le_mul_of_nonneg_right (by rw [hα₁]; linarith) hB₁c.le
    have hA₂c : α₁ * B₂.card ≤ A₂.card := by
      rw [hA₂, card_transl]
      exact mul_le_mul_of_nonneg_right (by rw [hα₁]; linarith) hB₂c.le
    have hA₂A₁ : A₂ ⊆ A₁ := transl_mono A (bohr_mono hρ₂ρ₁) x₀
    by_cases hB : 4 ≤ α₁ ^ 2 * B₁.card
    · right
      obtain ⟨Γ'', ρ₃, hc, hl, hρ₃, hu, hreg₃, x, hx⟩ := increment_main hN hℓ hΓ hρ₁ (by linarith)
        hreg₁ hρ₂ h₂u hreg₂ (transl_subset A B₁ x₀) (hT.transl B₁ x₀) hA₂A₁
        (transl_subset A B₂ x₀) (by rw [hα₁]; linarith) hA₁c hA₂c hB
      refine ⟨Γ'', ρ₃, hc, ?_, hρ₃, by linarith, hreg₃, x + x₀, ?_⟩
      · have := chain_upper hκ.le (by have := LcP_pos ℓ; positivity) hρ.le h₁l h₂l hl
        rw [FP]; exact this
      · refine le_trans ?_ (relDens_transl_le A B₁ _ x₀ x)
        refine le_trans ?_ hx
        have e : (A₁.card : ℝ) / B₁.card = relDens A B₁ x₀ := by
          rw [hA₁, card_transl]; field_simp
        rw [e]
        have hα0 : 0 < α := by linarith
        linarith
    · left
      push_neg at hB
      have h1 : (N : ℝ) * (ρ₁ / 2) ^ d ≤ B₁.card := card_bohr_ge Γ hρ₁ (by linarith)
      have h2 : (κ * ρ / 4) ^ d ≤ (ρ₁ / 2) ^ d :=
        pow_le_pow_left₀ (by positivity) (by linarith) d
      have h3 : (N : ℝ) * (κ * ρ / 4) ^ d ≤ (N : ℝ) * (ρ₁ / 2) ^ d :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have hα₁a : 49 / 50 * a ≤ α₁ := by rw [hα₁]; linarith
      have h4 : B₁.card < 4 / α₁ ^ 2 := by
        have hα₁0 : 0 < α₁ := by linarith
        rw [lt_div_iff₀ (by positivity)]; linarith
      have h5 : 4 / α₁ ^ 2 ≤ 4 / (49 / 50 * a) ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hα₁a 2
      linarith

end

end KM

end KMFile_IncrementFull

section KMFile_Iter



/-!
# Iterating the density increment
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

lemma relDens_le_one (A B : Finset (ZMod N)) (x : ZMod N) : relDens A B x ≤ 1 := by
  unfold relDens
  by_cases h : B.card = 0
  · simp [h]
  · rw [div_le_one (by positivity)]
    have : (A.filter fun a => a - x ∈ B).card ≤ B.card := by
      refine card_le_card_of_injOn (fun a => a - x) (fun a ha => (mem_filter.mp ha).2) ?_
      intro a _ b _ hab; simpa using hab
    exact_mod_cast this

/-- The state of the iteration after `n` steps. -/
def IterState (A : Finset (ZMod N)) (ℓ n : ℕ) : Prop :=
  ∃ Γ : Finset (ZMod N), ∃ ρ : ℝ, ∃ x : ZMod N, Γ.card ≤ n * LcP ℓ ∧ FP ℓ ^ n / 2 ≤ ρ ∧ 0 < ρ ∧
    ρ ≤ 1 / 2 ∧ IsReg Γ ρ (κP ℓ) (32 * κP ℓ * Γ.card) ∧
    (101 / 100 : ℝ) ^ n * aP ℓ ≤ relDens A (bohr Γ ρ) x

/-- The terminal alternative. -/
def Terminal (N ℓ : ℕ) : Prop :=
  (N : ℝ) * (κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4) ^ DmP ℓ < 4 / (49 / 50 * aP ℓ) ^ 2

lemma iter_zero {A : Finset (ZMod N)} {ℓ : ℕ} (hA : aP ℓ * N ≤ A.card) : IterState A ℓ 0 := by
  refine ⟨∅, 1 / 2, 0, by simp, by norm_num, by norm_num, le_rfl, ?_, ?_⟩
  · unfold IsReg; simp
  · rw [pow_zero, one_mul, relDens, bohr_empty, card_univ, ZMod.card]
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [le_div_iff₀ hN]
    simpa using hA

omit [NeZero N] in
lemma terminal_of_small {ℓ : ℕ} {d : ℕ} (hd : d ≤ DmP ℓ) {ρ : ℝ}
    (hρ : FP ℓ ^ (100 * ℓ) / 2 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    (h : (N : ℝ) * (κP ℓ * ρ / 4) ^ d < 4 / (49 / 50 * aP ℓ) ^ 2) : Terminal N ℓ := by
  unfold Terminal
  have hκ := κP_pos ℓ
  have hκ1 : κP ℓ ≤ 1 := by have := κP_le ℓ; linarith
  have hF := FP_pos ℓ
  have h0 : 0 ≤ κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4 := by positivity
  have h1 : κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4 ≤ κP ℓ * ρ / 4 := by gcongr
  have h2 : κP ℓ * ρ / 4 ≤ 1 := by
    have : κP ℓ * ρ ≤ 1 * (1 / 2) := mul_le_mul hκ1 hρ1 (by linarith [hρ, (by positivity : 0 ≤ FP ℓ ^ (100 * ℓ) / 2)]) (by norm_num)
    linarith
  have h3 : (κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4) ^ DmP ℓ ≤ (κP ℓ * ρ / 4) ^ d := by
    calc (κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4) ^ DmP ℓ ≤ (κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4) ^ d :=
          pow_le_pow_of_le_one h0 (h1.trans h2) hd
      _ ≤ (κP ℓ * ρ / 4) ^ d := pow_le_pow_left₀ h0 h1 d
  have hN : (0 : ℝ) ≤ N := by positivity
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h3 hN) h

lemma iter_succ (hN : Odd N) {A : Finset (ZMod N)} (hT : Tri A) {ℓ n : ℕ} (hℓ : 1 ≤ ℓ)
    (hn : n + 1 ≤ 100 * ℓ) (h : IterState A ℓ n) : IterState A ℓ (n + 1) ∨ Terminal N ℓ := by
  obtain ⟨Γ, ρ, x, hΓ, hρl, hρ, hρ1, hreg, hdens⟩ := h
  have hΓ' : Γ.card + LcP ℓ ≤ DmP ℓ := by
    rw [DmP]
    have : n * LcP ℓ + LcP ℓ ≤ 100 * ℓ * LcP ℓ := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hn
    omega
  set B := bohr Γ ρ with hB
  have hBc : (0 : ℝ) ≤ B.card := by positivity
  have hAx : (101 / 100 : ℝ) ^ n * aP ℓ * B.card ≤ (transl A B x).card := by
    rw [card_transl]; exact mul_le_mul_of_nonneg_right hdens hBc
  have hαa : aP ℓ ≤ (101 / 100 : ℝ) ^ n * aP ℓ :=
    le_mul_of_one_le_left (aP_pos ℓ).le (one_le_pow₀ (by norm_num))
  rcases increment hN hℓ hΓ' hρ hρ1 hreg (transl_subset A B x) (hT.transl B x) hαa hAx with
    hterm | ⟨Γ', ρ', hc, hl, hρ', hρ'1, hreg', x', hx'⟩
  · right
    have hn' : n ≤ 100 * ℓ := by omega
    refine terminal_of_small (by omega) ?_ hρ1 hterm
    refine le_trans ?_ hρl
    have hF := FP_pos ℓ
    have hF1 : FP ℓ ≤ 1 := by
      have := FP_le ℓ; have := κP_le ℓ; have := κP_pos ℓ; nlinarith
    have := pow_le_pow_of_le_one hF.le hF1 hn'
    linarith
  · left
    refine ⟨Γ', ρ', x' + x, ?_, ?_, hρ', hρ'1, hreg', ?_⟩
    · rw [Nat.succ_mul]; omega
    · rw [pow_succ]
      have := mul_le_mul_of_nonneg_left hρl (FP_pos ℓ).le
      have e : FP ℓ ^ n * FP ℓ / 2 = FP ℓ * (FP ℓ ^ n / 2) := by ring
      rw [e]; linarith
    · refine le_trans ?_ (relDens_transl_le A B _ x x')
      refine le_trans (le_of_eq ?_) hx'
      ring

theorem iter_all (hN : Odd N) {A : Finset (ZMod N)} (hT : Tri A) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hA : aP ℓ * N ≤ A.card) : ∀ n, n ≤ 100 * ℓ → IterState A ℓ n ∨ Terminal N ℓ := by
  intro n
  induction n with
  | zero => intro _; exact Or.inl (iter_zero hA)
  | succ n ih =>
    intro hn
    rcases ih (by omega) with h | h
    · exact iter_succ hN hT hℓ hn h
    · exact Or.inr h

lemma pow_101_gt {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 1 < (101 / 100 : ℝ) ^ (100 * ℓ) * aP ℓ := by
  rw [aP, pow_mul, ← mul_pow]
  have : 1 < (101 / 100 : ℝ) ^ 100 * (1 / 2) := by norm_num
  exact one_lt_pow₀ this (by omega)

/-- **Core bound.** A 3AP-trivial subset of `ZMod N` (`N` odd) of density at least `2^{-ℓ}`
forces `N` to be bounded. -/
theorem km_core (hN : Odd N) {A : Finset (ZMod N)} (hT : Tri A) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hA : aP ℓ * N ≤ A.card) : Terminal N ℓ := by
  rcases iter_all hN hT hℓ hA (100 * ℓ) le_rfl with h | h
  · exfalso
    obtain ⟨Γ, ρ, x, -, -, -, -, -, hdens⟩ := h
    have := relDens_le_one A (bohr Γ ρ) x
    have := pow_101_gt hℓ
    linarith
  · exact h

end

end KM

end KMFile_Iter

section KMFile_Bounds



/-!
# Explicit form of the core bound: `N ≤ 2^{2^{102} ℓ^{11}}`
-/

open Finset

namespace KM

noncomputable section

lemma rP_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : rP ℓ ≤ 16130 * ℓ ^ 2 := by
  rw [rP, PP_eq]; nlinarith

lemma kP_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : kP ℓ ≤ 12 * ℓ := by rw [kP]; omega

lemma LcP_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : LcP ℓ ≤ 2 ^ 78 * ℓ ^ 8 := by
  have hr := rP_le hℓ
  have hk := kP_le hℓ
  have hcs : csP ℓ ≤ 20480000 * (16130 * ℓ ^ 2) ^ 2 * (12 * ℓ) ^ 2 := by
    rw [csP_eq]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr 2))
      (Nat.pow_le_pow_left hk 2)
  have h1 : rP ℓ * csP ℓ ≤ (16130 * ℓ ^ 2) * (20480000 * (16130 * ℓ ^ 2) ^ 2 * (12 * ℓ) ^ 2) :=
    Nat.mul_le_mul hr hcs
  have h8 : 1 ≤ ℓ ^ 8 := Nat.one_le_pow _ _ hℓ
  rw [LcP]
  have e : (16130 * ℓ ^ 2) * (20480000 * (16130 * ℓ ^ 2) ^ 2 * (12 * ℓ) ^ 2) =
      12376434466160640000000 * ℓ ^ 8 := by ring
  rw [e] at h1
  have : (2 : ℕ) ^ 78 = 302231454903657293676544 := by norm_num
  rw [this]
  nlinarith

lemma DmP_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : DmP ℓ ≤ 2 ^ 85 * ℓ ^ 9 := by
  rw [DmP]
  have := LcP_le hℓ
  calc 100 * ℓ * LcP ℓ ≤ 100 * ℓ * (2 ^ 78 * ℓ ^ 8) := Nat.mul_le_mul_left _ this
    _ = 100 * 2 ^ 78 * ℓ ^ 9 := by ring
    _ ≤ 2 ^ 85 * ℓ ^ 9 := Nat.mul_le_mul_right _ (by norm_num)

lemma pow_le_two_pow (ℓ m : ℕ) : ℓ ^ m ≤ 2 ^ (m * ℓ) := by
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le m

lemma den_κ_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 6400 * (DmP ℓ + 1) ≤ 2 ^ (108 * ℓ) := by
  have h1 := DmP_le hℓ
  have h2 := pow_le_two_pow ℓ 9
  have h3 : 6400 * (DmP ℓ + 1) ≤ 2 ^ 99 * 2 ^ (9 * ℓ) := by
    have : 1 ≤ 2 ^ (9 * ℓ) := Nat.one_le_two_pow
    have : 1 ≤ ℓ ^ 9 := Nat.one_le_pow _ _ hℓ
    nlinarith
  refine h3.trans ?_
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma den_F_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 409600 * LcP ℓ ≤ 2 ^ (105 * ℓ) := by
  have h1 := LcP_le hℓ
  have h2 := pow_le_two_pow ℓ 8
  have h3 : 409600 * LcP ℓ ≤ 2 ^ 97 * 2 ^ (8 * ℓ) := by
    nlinarith
  refine h3.trans ?_
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma κP_ge {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : (1 / 2 : ℝ) ^ (109 * ℓ) ≤ κP ℓ := by
  rw [κP, aP]
  have h := den_κ_le hℓ
  have h' : (6400 * ((DmP ℓ : ℝ) + 1)) ≤ 2 ^ (108 * ℓ) := by exact_mod_cast h
  rw [le_div_iff₀ (by positivity)]
  calc (1 / 2 : ℝ) ^ (109 * ℓ) * (6400 * ((DmP ℓ : ℝ) + 1)) ≤
      (1 / 2 : ℝ) ^ (109 * ℓ) * 2 ^ (108 * ℓ) := by gcongr
    _ = (1 / 2) ^ ℓ := by
      rw [show 109 * ℓ = ℓ + 108 * ℓ by ring, pow_add, mul_assoc, ← mul_pow]; norm_num

lemma FP_ge {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : (1 / 2 : ℝ) ^ (868 * ℓ) ≤ FP ℓ := by
  rw [FP]
  have h := den_F_le hℓ
  have h' : (409600 * (LcP ℓ : ℝ)) ≤ 2 ^ (105 * ℓ) := by exact_mod_cast h
  have hL : (0 : ℝ) < LcP ℓ := by have := LcP_pos ℓ; positivity
  rw [le_div_iff₀ (by positivity)]
  have hκ7 : ((1 / 2 : ℝ) ^ (109 * ℓ)) ^ 7 ≤ κP ℓ ^ 7 :=
    pow_le_pow_left₀ (by positivity) (κP_ge hℓ) 7
  calc (1 / 2 : ℝ) ^ (868 * ℓ) * (409600 * (LcP ℓ : ℝ)) ≤
      (1 / 2 : ℝ) ^ (868 * ℓ) * 2 ^ (105 * ℓ) := by gcongr
    _ = ((1 / 2 : ℝ) ^ (109 * ℓ)) ^ 7 := by
      rw [← pow_mul, show 868 * ℓ = 109 * ℓ * 7 + 105 * ℓ by ring, pow_add, mul_assoc,
        ← mul_pow]; norm_num
    _ ≤ κP ℓ ^ 7 := hκ7

lemma base_ge {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (1 / 2 : ℝ) ^ (86912 * ℓ ^ 2) ≤ κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4 := by
  have h1 := κP_ge hℓ
  have h2 : ((1 / 2 : ℝ) ^ (868 * ℓ)) ^ (100 * ℓ) ≤ FP ℓ ^ (100 * ℓ) :=
    pow_le_pow_left₀ (by positivity) (FP_ge hℓ) _
  have e : κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4 = κP ℓ * FP ℓ ^ (100 * ℓ) * (1 / 2) ^ 3 := by ring
  rw [e]
  have hκ0 := (κP_pos ℓ).le
  have h3 : (1 / 2 : ℝ) ^ (109 * ℓ) * ((1 / 2 : ℝ) ^ (868 * ℓ)) ^ (100 * ℓ) * (1 / 2) ^ 3 ≤
      κP ℓ * FP ℓ ^ (100 * ℓ) * (1 / 2) ^ 3 := by
    gcongr
  refine le_trans ?_ h3
  rw [← pow_mul, ← pow_add, ← pow_add]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  nlinarith

lemma rhs_le (ℓ : ℕ) : 4 / (49 / 50 * aP ℓ) ^ 2 ≤ 2 ^ (2 * ℓ + 3) := by
  rw [aP, div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ (2 * ℓ + 3) * (49 / 50 * (1 / 2) ^ ℓ) ^ 2 = 8 * (49 / 50) ^ 2 := by
    rw [mul_pow, ← pow_mul, pow_add, show ℓ * 2 = 2 * ℓ by ring]
    have : (2 : ℝ) ^ (2 * ℓ) * ((1 / 2) ^ (2 * ℓ)) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (8 * (49 / 50 : ℝ) ^ 2) * this
  rw [this]; norm_num

/-- **Kelley–Meka core bound, explicit form.** -/
theorem km_bound {N : ℕ} [NeZero N] (hN : Odd N) {A : Finset (ZMod N)} (hT : Tri A) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hA : (1 / 2 : ℝ) ^ ℓ * N ≤ A.card) :
    (N : ℝ) ≤ 2 ^ (2 ^ 102 * ℓ ^ 11) := by
  have h := km_core hN hT hℓ hA
  unfold Terminal at h
  set y := κP ℓ * (FP ℓ ^ (100 * ℓ) / 2) / 4 with hy
  have hy1 := base_ge hℓ
  have hD := DmP_le hℓ
  have hyD : (1 / 2 : ℝ) ^ (86912 * 2 ^ 85 * ℓ ^ 11) ≤ y ^ DmP ℓ := by
    have hy0 : 0 ≤ (1 / 2 : ℝ) ^ (86912 * ℓ ^ 2) := by positivity
    have hy1' : (1 / 2 : ℝ) ^ (86912 * ℓ ^ 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (1 / 2 : ℝ) ^ (86912 * 2 ^ 85 * ℓ ^ 11) = ((1 / 2 : ℝ) ^ (86912 * ℓ ^ 2)) ^ (2 ^ 85 * ℓ ^ 9) := by
          rw [← pow_mul]; ring_nf
      _ ≤ ((1 / 2 : ℝ) ^ (86912 * ℓ ^ 2)) ^ DmP ℓ := pow_le_pow_of_le_one hy0 hy1' hD
      _ ≤ y ^ DmP ℓ := pow_le_pow_left₀ hy0 hy1 _
  have hrhs := rhs_le ℓ
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have h2 : (N : ℝ) * (1 / 2 : ℝ) ^ (86912 * 2 ^ 85 * ℓ ^ 11) ≤ 2 ^ (2 * ℓ + 3) := by
    have := mul_le_mul_of_nonneg_left hyD hN0
    linarith
  have e : (N : ℝ) = (N : ℝ) * (1 / 2 : ℝ) ^ (86912 * 2 ^ 85 * ℓ ^ 11) *
      2 ^ (86912 * 2 ^ 85 * ℓ ^ 11) := by
    rw [mul_assoc, ← mul_pow]; norm_num
  rw [e]
  calc (N : ℝ) * (1 / 2 : ℝ) ^ (86912 * 2 ^ 85 * ℓ ^ 11) * 2 ^ (86912 * 2 ^ 85 * ℓ ^ 11) ≤
      2 ^ (2 * ℓ + 3) * 2 ^ (86912 * 2 ^ 85 * ℓ ^ 11) := by gcongr
    _ = 2 ^ (2 * ℓ + 3 + 86912 * 2 ^ 85 * ℓ ^ 11) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (2 ^ 102 * ℓ ^ 11) := by
      apply pow_le_pow_right₀ (by norm_num)
      have : ℓ ≤ ℓ ^ 11 := Nat.le_self_pow (by norm_num) ℓ
      have : 1 ≤ ℓ ^ 11 := Nat.one_le_pow _ _ hℓ
      have e2 : (2 : ℕ) ^ 102 = 131072 * 2 ^ 85 := by norm_num
      rw [e2]
      nlinarith

end

end KM

end KMFile_Bounds

section KMFile_Final



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

/-- If every subset of `{1, …, N}` of size at least `c` contains a `k`-term progression, then
`r k N < c`. -/
theorem r_lt_of' (k N : ℕ) (hk : 1 < k) (c : ℝ)
    (h : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → c ≤ S.card →
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) : (Erdos142.r k N : ℝ) < c := by
  have hne : {x | ∃ (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : Erdos142.IsAPOfLengthFree (S : Set ℕ) k), S.card = x}.Nonempty :=
    ⟨0, ∅, by simp, by simpa using Erdos142.isAPOfLengthFree_empty (α := ℕ) k, rfl⟩
  have hbdd : BddAbove {x | ∃ (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : Erdos142.IsAPOfLengthFree (S : Set ℕ) k), S.card = x} := by
    refine ⟨N, ?_⟩
    rintro m ⟨T, hT, -, rfl⟩
    simpa using (Finset.card_le_card hT).trans_eq (by simp)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hne hbdd
  by_contra hc
  push_neg at hc
  have hr : Erdos142.r k N = S.card := by
    rw [Erdos142.r, ← hcard]
  rw [hr] at hc
  obtain ⟨a, d, hd, hap⟩ := h S hS hc
  exact not_isAPOfLengthFree_of_ap' k hk S a d hd hap hfree

lemma natCast_eq_of_lt {N a b : ℕ} (ha : a < N) (hb : b < N) (h : (a : ZMod N) = b) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff' a b N, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

lemma tri_of_noAP {M : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 M)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ S) :
    Tri (S.image (Nat.cast : ℕ → ZMod (2 * M + 1))) := by
  intro a ha b hb c hc e
  rw [mem_image] at ha hb hc
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hc
  have ha1 := mem_Icc.mp (hS ha')
  have hb1 := mem_Icc.mp (hS hb')
  have hc1 := mem_Icc.mp (hS hc')
  have e' : a' + c' = b' + b' := by
    apply natCast_eq_of_lt (N := 2 * M + 1) (by omega) (by omega)
    push_cast; exact e
  by_contra hab
  have hab' : a' ≠ b' := fun h => hab (by rw [h])
  apply hno
  rcases lt_or_gt_of_ne hab' with h | h
  · refine ⟨a', b' - a', by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using ha'
    · rw [show a' + 1 * (b' - a') = b' by omega]; exact hb'
    · rw [show a' + 2 * (b' - a') = c' by omega]; exact hc'
  · refine ⟨c', a' - b', by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hc'
    · rw [show c' + 1 * (a' - b') = b' by omega]; exact hb'
    · rw [show c' + 2 * (a' - b') = a' by omega]; exact ha'

lemma card_image_natCast {M : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 M) :
    (S.image (Nat.cast : ℕ → ZMod (2 * M + 1))).card = S.card := by
  apply card_image_of_injOn
  intro a ha b hb hab
  have ha1 := mem_Icc.mp (hS ha)
  have hb1 := mem_Icc.mp (hS hb)
  exact natCast_eq_of_lt (by omega) (by omega) hab

/-- The core bound transferred to subsets of `{1, …, M}` without 3-term progressions. -/
theorem bound_of_noAP {M : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 M)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ S) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (h : (1 / 2 : ℝ) ^ ℓ * (2 * M + 1) ≤ S.card) :
    (2 * M + 1 : ℝ) ≤ 2 ^ (2 ^ 102 * ℓ ^ 11) := by
  haveI : NeZero (2 * M + 1) := ⟨by omega⟩
  have := km_bound (N := 2 * M + 1) ⟨M, rfl⟩ (tri_of_noAP hS hno) hℓ
    (by rw [card_image_natCast hS]; push_cast; exact h)
  push_cast at this
  exact this

lemma rpow_twelfth_pow {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma two_pow_ge {u : ℝ} (hu : 0 ≤ u) {ℓ : ℕ} (hℓ : 2 * u + 2 ≤ ℓ) :
    3 * Real.exp u ≤ 2 ^ ℓ := by
  have hl2 := Real.log_two_gt_d9
  have e : (2 : ℝ) ^ ℓ = Real.exp (ℓ * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [e]
  have h1 : u + Real.log 3 ≤ ℓ * Real.log 2 := by
    have hl3 : Real.log 3 < 2 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    have i1 : (2 * u + 2) * Real.log 2 ≤ ℓ * Real.log 2 :=
      mul_le_mul_of_nonneg_right hℓ (by linarith)
    have i2 : 0 ≤ u * (2 * Real.log 2 - 1) := mul_nonneg hu (by linarith)
    nlinarith
  calc 3 * Real.exp u = Real.exp (u + Real.log 3) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]; ring
    _ ≤ Real.exp (ℓ * Real.log 2) := Real.exp_le_exp.mpr h1

/-- **Kelley–Meka.** `r_3(N) ≤ N exp(-(log N)^{1/12})` for all large `N`. -/
theorem kelley_meka_main :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (Erdos142.r 3 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12)) := by
  refine ⟨1, one_pos, ?_⟩
  set T : ℝ := 2 ^ 102 * 3 ^ 11 + 3 with hT
  have hT0 : 0 < T := by positivity
  rw [Filter.eventually_atTop]
  refine ⟨⌈Real.exp (T ^ 12)⌉₊ + 1, fun M hM => ?_⟩
  have hMpos : (1 : ℝ) ≤ M := by
    have : 1 ≤ M := by omega
    exact_mod_cast this
  have hMexp : Real.exp (T ^ 12) ≤ M := by
    have := Nat.le_ceil (Real.exp (T ^ 12))
    have : (⌈Real.exp (T ^ 12)⌉₊ : ℝ) ≤ M := by exact_mod_cast (by omega : ⌈Real.exp (T ^ 12)⌉₊ ≤ M)
    linarith
  have hlogM : T ^ 12 ≤ Real.log M := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hMexp
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg hMpos
  set u := Real.log M ^ ((1 : ℝ) / 12) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hlog0 _
  have huT : T ≤ u := by
    have := Real.rpow_le_rpow (by positivity) hlogM (by norm_num : (0 : ℝ) ≤ 1 / 12)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, show ((12 : ℕ) : ℝ) * (1 / 12) = 1 by
      norm_num, Real.rpow_one] at this
  have hu12 : u ^ 12 = Real.log M := rpow_twelfth_pow hlog0
  rw [neg_one_mul]
  refine (r_lt_of' 3 M (by norm_num) _ fun S hS hc => ?_).le
  by_contra hno
  set ℓ := ⌈2 * u⌉₊ + 2 with hℓ
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓu : 2 * u + 2 ≤ ℓ := by
    have := Nat.le_ceil (2 * u)
    rw [hℓ]; push_cast; linarith
  have hℓu' : (ℓ : ℝ) ≤ 2 * u + 3 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * u)
    rw [hℓ]; push_cast; linarith
  have h2 := two_pow_ge hu0 hℓu
  have hdens : (1 / 2 : ℝ) ^ ℓ * (2 * M + 1) ≤ S.card := by
    refine le_trans ?_ hc
    have hexp : 0 < Real.exp u := Real.exp_pos u
    rw [Real.exp_neg, one_div_pow, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    have : (M : ℝ) * (Real.exp u)⁻¹ * 2 ^ ℓ ≥ (M : ℝ) * (Real.exp u)⁻¹ * (3 * Real.exp u) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e : (M : ℝ) * (Real.exp u)⁻¹ * (3 * Real.exp u) = 3 * M := by field_simp
    linarith
  have hb := bound_of_noAP hS hno hℓ1 hdens
  -- take logarithms
  have hlog : Real.log M ≤ 2 ^ 102 * (ℓ : ℝ) ^ 11 := by
    have h1 : Real.log M ≤ Real.log (2 * M + 1) := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 * M + 1) ≤ Real.log (2 ^ (2 ^ 102 * ℓ ^ 11)) :=
      Real.log_le_log (by positivity) hb
    rw [Real.log_pow] at h2
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : ((2 ^ 102 * ℓ ^ 11 : ℕ) : ℝ) * Real.log 2 ≤ ((2 ^ 102 * ℓ ^ 11 : ℕ) : ℝ) :=
      mul_le_of_le_one_right (by positivity) hl2.le
    push_cast at this h2
    linarith
  have hu3 : 3 ≤ u := by linarith
  have hℓ3 : (ℓ : ℝ) ≤ 3 * u := by linarith
  have h11 : (ℓ : ℝ) ^ 11 ≤ (3 * u) ^ 11 := pow_le_pow_left₀ (by positivity) hℓ3 11
  have hfin : u ^ 12 ≤ 2 ^ 102 * 3 ^ 11 * u ^ 11 := by
    rw [hu12]
    calc Real.log M ≤ 2 ^ 102 * (ℓ : ℝ) ^ 11 := hlog
      _ ≤ 2 ^ 102 * (3 * u) ^ 11 := by gcongr
      _ = 2 ^ 102 * 3 ^ 11 * u ^ 11 := by ring
  have hu11 : 0 < u ^ 11 := by positivity
  have : u ≤ 2 ^ 102 * 3 ^ 11 := by
    have e : u ^ 12 = u * u ^ 11 := by ring
    rw [e] at hfin
    exact le_of_mul_le_mul_right hfin hu11
  linarith

end

end KM

namespace Erdos142

/-- **Kelley–Meka (2023).** There is `c > 0` with `r_3(N) ≤ N exp(-c (log N)^{1/12})` for all
large `N` (we can take `c = 1`). -/
theorem kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r 3 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12)) :=
  KM.kelley_meka_main

end Erdos142

end KMFile_Final

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (Erdos142.r 3 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12)) :=
  Erdos142.kelley_meka
