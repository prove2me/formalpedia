-- Prove2me | solution 1 for CannonFloydParry.exists_mulEquiv_SigmaPres_SigmaPerm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T10:53:59.492991+00:00
-- url     : https://prove2.me/submissions/4e23e7ec-ef3e-42c0-a668-3cbfba1354b7

import Mathlib
import Definitions.Def_CannonFloydParry_V

/-! A coset count for elements satisfying the relations of Σ's presentation (CFP p. 247):
if `t₀, t₁, …` are involutions with `(tᵢtᵢ₊₁)³ = 1` and `tᵢtⱼ = tⱼtᵢ` for `j ≥ i + 2`, then
`⟨t₀, …, t_{n-1}⟩` has at most `(n + 1)!` elements. -/

namespace CannonFloydParry.S6.CoxA

variable {G : Type*} [Group G]

/-- The relations of the presentation of `Σ` on p. 247, for a sequence `t` in `G`. -/
structure IsCoxA (t : ℕ → G) : Prop where
  sq : ∀ i, t i * t i = 1
  cube : ∀ i, (t i * t (i + 1)) ^ 3 = 1
  comm : ∀ i j, i + 2 ≤ j → t i * t j = t j * t i

/-- `⟨t₀, …, t_{n-1}⟩`. -/
def Sub (t : ℕ → G) (n : ℕ) : Subgroup G := Subgroup.closure (t '' Set.Iio n)

/-- `W t j s = t_{j+s-1} ⋯ t_{j+1} t_j`. -/
def W (t : ℕ → G) (j : ℕ) : ℕ → G
  | 0 => 1
  | s + 1 => t (j + s) * W t j s

variable {t : ℕ → G}

lemma W_succ (j s : ℕ) : W t j (s + 1) = t (j + s) * W t j s := rfl

lemma W_split (j a b : ℕ) : W t j (a + b) = W t (j + b) a * W t j b := by
  induction a with
  | zero => simp [W]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, W_succ, ih, W_succ,
      show j + b + a = j + (a + b) by omega, mul_assoc]

lemma W_bottom (j s : ℕ) : W t j (s + 1) = W t (j + 1) s * t j := by
  rw [W_split j s 1]; simp [W]

lemma Sub_mono {a b : ℕ} (h : a ≤ b) : Sub t a ≤ Sub t b :=
  Subgroup.closure_mono (Set.image_mono (Set.Iio_subset_Iio h))

lemma t_mem {i n : ℕ} (h : i < n) : t i ∈ Sub t n := Subgroup.subset_closure ⟨i, h, rfl⟩

lemma W_mem (j n : ℕ) : ∀ s, j + s ≤ n → W t j s ∈ Sub t n := by
  intro s
  induction s with
  | zero => intro; exact one_mem _
  | succ s ih => intro h; rw [W_succ]; exact mul_mem (t_mem (by omega)) (ih (by omega))

namespace IsCoxA

variable (h : IsCoxA t)
include h

lemma inv (i : ℕ) : (t i)⁻¹ = t i := inv_eq_of_mul_eq_one_right (h.sq i)

lemma commute (x y : ℕ) (hxy : x + 2 ≤ y ∨ y + 2 ≤ x) : Commute (t x) (t y) := by
  rcases hxy with hxy | hxy
  · exact h.comm x y hxy
  · exact (h.comm y x hxy).symm

lemma braid (i : ℕ) : t (i + 1) * t i * t (i + 1) = t i * t (i + 1) * t i := by
  have e : t (i + 1) * t i * t (i + 1) =
      (t i * t (i + 1) * t i)⁻¹ * (t i * t (i + 1)) ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [e, h.cube, mul_one]
  simp only [mul_inv_rev, h.inv]
  group

lemma W_comm (x j : ℕ) : ∀ s, (∀ y, j ≤ y → y < j + s → x + 2 ≤ y ∨ y + 2 ≤ x) →
    Commute (t x) (W t j s) := by
  intro s
  induction s with
  | zero => intro; exact Commute.one_right _
  | succ s ih =>
    intro hy
    rw [W_succ]
    exact (h.commute x (j + s) (hy _ (by omega) (by omega))).mul_right
      (ih fun y h1 h2 => hy y h1 (by omega))

lemma step (k j i : ℕ) (hj : j ≤ k + 1) (hi : i < k + 1) :
    ∃ j', j' ≤ k + 1 ∧ ∃ h' ∈ Sub t k, W t j (k + 1 - j) * t i = h' * W t j' (k + 1 - j') := by
  rcases (show i + 2 ≤ j ∨ i + 1 = j ∨ i = j ∨ j < i by omega) with hc | hc | hc | hc
  · refine ⟨j, hj, t i, t_mem (by omega), ?_⟩
    exact (h.W_comm i j _ (fun y h1 _ => Or.inl (by omega))).eq.symm
  · subst hc
    refine ⟨i, by omega, 1, one_mem _, ?_⟩
    rw [one_mul, show k + 1 - i = (k + 1 - (i + 1)) + 1 by omega, W_bottom]
  · subst hc
    refine ⟨i + 1, by omega, 1, one_mem _, ?_⟩
    rw [one_mul, show k + 1 - i = (k + 1 - (i + 1)) + 1 by omega, W_bottom, mul_assoc, h.sq,
      mul_one]
  · obtain ⟨a, b, ha, hb⟩ : ∃ a b, a = k - i ∧ b = i - 1 - j := ⟨_, _, rfl, rfl⟩
    obtain ⟨c, rfl⟩ : ∃ c, i = c + 1 := ⟨i - 1, by omega⟩
    have ht : k + 1 - j = (a + 2) + b := by omega
    have hcb : j + b = c := by omega
    refine ⟨j, hj, t c, t_mem (by omega), ?_⟩
    have e1 : W t j (k + 1 - j) = W t (c + 2) a * (t (c + 1) * t c) * W t j b := by
      rw [ht, W_split j (a + 2) b, hcb, W_split c a 2]
      simp [W]
    have cb : Commute (t (c + 1)) (W t j b) :=
      h.W_comm (c + 1) j b (fun y h1 h2 => Or.inr (by omega))
    have ca : Commute (t c) (W t (c + 2) a) :=
      h.W_comm c (c + 2) a (fun y h1 h2 => Or.inl (by omega))
    rw [e1]
    calc W t (c + 2) a * (t (c + 1) * t c) * W t j b * t (c + 1)
        = W t (c + 2) a * (t (c + 1) * t c) * (W t j b * t (c + 1)) := by group
      _ = W t (c + 2) a * (t (c + 1) * t c * t (c + 1)) * W t j b := by rw [← cb.eq]; group
      _ = W t (c + 2) a * (t c * t (c + 1) * t c) * W t j b := by rw [h.braid]
      _ = (W t (c + 2) a * t c) * (t (c + 1) * t c) * W t j b := by group
      _ = _ := by rw [← ca.eq]; group

lemma cover (k : ℕ) {g : G} (hg : g ∈ Sub t (k + 1)) :
    ∃ j, j ≤ k + 1 ∧ ∃ x ∈ Sub t k, g = x * W t j (k + 1 - j) := by
  unfold Sub at hg
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨k + 1, le_rfl, 1, one_mem _, by simp [W]⟩
  | mul_right x hx y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨j, hj, z, hz, rfl⟩ := ih
    obtain ⟨j', hj', z', hz', e⟩ := h.step k j i hj hi
    exact ⟨j', hj', z * z', mul_mem hz hz', by rw [mul_assoc, e, mul_assoc]⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨j, hj, z, hz, rfl⟩ := ih
    obtain ⟨j', hj', z', hz', e⟩ := h.step k j i hj hi
    exact ⟨j', hj', z * z', mul_mem hz hz', by rw [h.inv, mul_assoc, e, mul_assoc]⟩

/-- `⟨t₀, …, t_{n-1}⟩` is finite, with at most `(n + 1)!` elements. -/
lemma finite_card (n : ℕ) : Finite (Sub t n) ∧ Nat.card (Sub t n) ≤ (n + 1).factorial := by
  induction n with
  | zero =>
    have : Sub t 0 = ⊥ := by
      unfold Sub
      rw [show t '' Set.Iio 0 = ∅ by ext; simp, Subgroup.closure_empty]
    rw [this]
    exact ⟨inferInstance, by simp⟩
  | succ k ih =>
    obtain ⟨hfin, hcard⟩ := ih
    let f : Sub t k × Fin (k + 2) → Sub t (k + 1) := fun p =>
      ⟨p.1 * W t p.2 (k + 1 - p.2), mul_mem (Sub_mono (by omega) p.1.2) (W_mem _ _ _ (by omega))⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨j, hj, x, hx, rfl⟩ := h.cover k hg
      exact ⟨(⟨x, hx⟩, ⟨j, by omega⟩), rfl⟩
    refine ⟨Finite.of_surjective f hf, ?_⟩
    calc Nat.card (Sub t (k + 1)) ≤ Nat.card (Sub t k × Fin (k + 2)) :=
          Nat.card_le_card_of_surjective f hf
      _ = Nat.card (Sub t k) * (k + 2) := by rw [Nat.card_prod, Nat.card_fin]
      _ ≤ (k + 1).factorial * (k + 2) := Nat.mul_le_mul_right _ hcard
      _ = (k + 1 + 1).factorial := by rw [Nat.factorial_succ (k + 1)]; ring

end IsCoxA

end CannonFloydParry.S6.CoxA

/-! In every proper quotient of `Σ`, `s₀` and `s₁` have the same image (CFP p. 247). -/

namespace CannonFloydParry.S6

open Equiv Equiv.Perm

instance (K : ℕ) : Fintype {x : ℕ // x < K} := Fintype.ofEquiv _ Fin.equivSubtype


end CannonFloydParry.S6

/-! The presentation of `Σ` (CFP p. 247). -/

namespace CannonFloydParry.S6

open Equiv Equiv.Perm CoxA

/-- `sᵢ` in the presented group. -/
abbrev sg (i : ℕ) : SigmaPres := PresentedGroup.of i

lemma relS {r : FreeGroup ℕ} (h : r ∈ relsSigma) : PresentedGroup.mk relsSigma r = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure h)

lemma isCoxA_sg : IsCoxA sg where
  sq i := by
    have := relS (Or.inl (Or.inl ⟨i, rfl⟩) : FreeGroup.of i ^ 2 ∈ relsSigma)
    rw [map_pow] at this; rw [← sq]; exact this
  cube i := by
    have := relS (Or.inl (Or.inr ⟨i, rfl⟩) :
      (FreeGroup.of i * FreeGroup.of (i + 1)) ^ 3 ∈ relsSigma)
    rwa [map_pow, map_mul] at this
  comm i j h := by
    have e := relS (Or.inr ⟨i, j, h, rfl⟩ : (FreeGroup.of i * FreeGroup.of j) ^ 2 ∈ relsSigma)
    rw [map_pow, map_mul] at e
    have hi : sg i * sg i = 1 := by
      have := relS (Or.inl (Or.inl ⟨i, rfl⟩) : FreeGroup.of i ^ 2 ∈ relsSigma)
      rw [map_pow] at this; rw [← sq]; exact this
    have hj : sg j * sg j = 1 := by
      have := relS (Or.inl (Or.inl ⟨j, rfl⟩) : FreeGroup.of j ^ 2 ∈ relsSigma)
      rw [map_pow] at this; rw [← sq]; exact this
    have ii : (sg i)⁻¹ = sg i := inv_eq_of_mul_eq_one_right hi
    have jj : (sg j)⁻¹ = sg j := inv_eq_of_mul_eq_one_right hj
    calc sg i * sg j = (sg i * sg j)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact e)).symm
      _ = sg j * sg i := by rw [mul_inv_rev, ii, jj]

lemma swap_cube (i : ℕ) : (swap i (i + 1) * swap (i + 1) (i + 1 + 1)) ^ 3 = 1 := by
  set a := swap i (i + 1)
  set b := swap (i + 1) (i + 1 + 1)
  have e : (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
    simp only [pow_succ, pow_zero, one_mul]; group
  have aba : a * b * a = swap i (i + 2) := by
    simp only [a, b]
    rw [swap_comm i (i + 1), swap_comm (i + 1) (i + 1 + 1),
      swap_mul_swap_mul_swap (x := i + 1 + 1) (y := i + 1) (z := i) (by omega) (by omega)]
  have bab : b * a * b = swap i (i + 2) := by
    simp only [a, b]
    rw [swap_mul_swap_mul_swap (x := i) (y := i + 1) (z := i + 1 + 1) (by omega) (by omega),
      swap_comm]
  rw [e, aba, bab, swap_mul_self]

lemma swap_far (i j : ℕ) (hij : i + 2 ≤ j) : (swap i (i + 1) * swap j (j + 1)) ^ 2 = 1 := by
  have hd : Perm.Disjoint (swap i (i + 1)) (swap j (j + 1)) := by
    intro x
    by_cases hx : x = i ∨ x = i + 1
    · right; exact swap_apply_of_ne_of_ne (by omega) (by omega)
    · left; push_neg at hx; exact swap_apply_of_ne_of_ne hx.1 hx.2
  rw [sq, mul_assoc, ← mul_assoc (swap j (j + 1)), ← hd.commute.eq, mul_assoc, swap_mul_self,
    mul_one, swap_mul_self]

lemma rels_swap : ∀ r ∈ relsSigma, FreeGroup.lift (fun i : ℕ => swap i (i + 1)) r = 1 := by
  rintro r ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, j, hij, rfl⟩)
  · simp only [map_pow, FreeGroup.lift_apply_of]
    rw [sq, swap_mul_self]
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
    exact swap_cube i
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
    exact swap_far i j hij

/-- `sᵢ ↦ (i i+1)`, into `Perm ℕ`. -/
noncomputable def phi0 : SigmaPres →* Perm ℕ := PresentedGroup.toGroup rels_swap

lemma phi0_sg (i : ℕ) : phi0 (sg i) = swap i (i + 1) := PresentedGroup.toGroup.of rels_swap

lemma mem_closure_of (g : SigmaPres) : g ∈ Subgroup.closure (Set.range (PresentedGroup.of : ℕ → SigmaPres)) := by
  rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top g

lemma phi0_mem (g : SigmaPres) : phi0 g ∈ SigmaPerm := by
  induction mem_closure_of g using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; rw [phi0_sg]; exact (sigmaGen i).2
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

/-- `sᵢ ↦ sᵢ`, into `Σ`. -/
noncomputable def phi : SigmaPres →* SigmaPerm := phi0.codRestrict SigmaPerm phi0_mem

lemma phi_sg (i : ℕ) : phi (sg i) = sigmaGen i := Subtype.ext (phi0_sg i)

/-- Every transposition `(a b)` with `a < b ≤ n` is the image of an element of level `n`. -/
lemma swap_mem_level (n a : ℕ) : ∀ d, a + d + 1 ≤ n →
    swap a (a + d + 1) ∈ (Sub sg n).map phi0 := by
  intro d
  induction d with
  | zero => intro h; exact ⟨sg a, t_mem (by omega), phi0_sg a⟩
  | succ d ih =>
    intro h
    have g : swap (a + d + 1) (a + d + 1 + 1) ∈ (Sub sg n).map phi0 :=
      ⟨sg (a + d + 1), t_mem (by omega), phi0_sg _⟩
    have e : swap a (a + (d + 1) + 1) =
        swap (a + d + 1) (a + d + 1 + 1) * swap a (a + d + 1) * swap (a + d + 1) (a + d + 1 + 1) := by
      rw [swap_mul_swap_mul_swap (by omega) (by omega), swap_comm]
      congr 1
    rw [e]
    exact mul_mem (mul_mem g (ih (by omega))) g

lemma swap_mem_level' (n : ℕ) {a b : ℕ} (hab : a ≠ b) (ha : a ≤ n) (hb : b ≤ n) :
    swap a b ∈ (Sub sg n).map phi0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
    exact swap_mem_level n a d hb
  · obtain ⟨d, rfl⟩ : ∃ d, a = b + d + 1 := ⟨a - b - 1, by omega⟩
    rw [swap_comm]; exact swap_mem_level n b d ha

lemma phi_surjective : Function.Surjective phi := by
  intro σ
  have hσ : (σ : Perm ℕ) ∈ Subgroup.closure {τ : Perm ℕ | τ.IsSwap} := by
    rw [mem_closure_isSwap']
    refine σ.2.subset fun x hx => ?_
    simpa [MulAction.mem_fixedBy, Perm.smul_def] using hx
  have hle : Subgroup.closure {τ : Perm ℕ | τ.IsSwap} ≤ phi0.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, b, hab, rfl⟩
    obtain ⟨g, -, hg⟩ := swap_mem_level' (max a b) hab (le_max_left _ _) (le_max_right _ _)
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hle hσ
  exact ⟨g, Subtype.ext hg⟩

lemma mem_some_level (g : SigmaPres) : ∃ n, g ∈ Sub sg n := by
  induction mem_closure_of g using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ⟨i + 1, t_mem (by omega)⟩
  | one => exact ⟨0, one_mem _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, mul_mem (Sub_mono (le_max_left _ _) ha) (Sub_mono (le_max_right _ _) hb)⟩
  | inv x _ hx => obtain ⟨a, ha⟩ := hx; exact ⟨a, inv_mem ha⟩

instance (K : ℕ) : Finite {x : ℕ // x < K} := Finite.of_equiv _ Fin.equivSubtype

/-- On each level, `phi0` is injective. -/
lemma level_injective (n : ℕ) {g : SigmaPres} (hg : g ∈ Sub sg n) (h1 : phi0 g = 1) : g = 1 := by
  obtain ⟨hfin, hcard⟩ := isCoxA_sg.finite_card n
  set L := Sub sg n
  set H := L.map phi0
  let f : L → H := fun x => ⟨phi0 x, x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  haveI : Finite H := Finite.of_surjective f hf
  have hsub : (ofSubtype : Perm {x : ℕ // x < n + 1} →* Perm ℕ).range ≤ H := by
    rw [MonoidHom.range_eq_map, ← closure_isSwap, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨τ, ⟨a, b, hab, rfl⟩, rfl⟩
    rw [ofSubtype_swap_eq]
    exact swap_mem_level' n (fun h => hab (Subtype.ext h)) (by have := a.2; omega)
      (by have := b.2; omega)
  have hlow : (n + 1).factorial ≤ Nat.card H := by
    calc (n + 1).factorial = Nat.card (Perm {x : ℕ // x < n + 1}) := by
          rw [Nat.card_perm, ← Nat.card_congr (Fin.equivSubtype (n := n + 1)), Nat.card_fin]
      _ = Nat.card (ofSubtype : Perm {x : ℕ // x < n + 1} →* Perm ℕ).range :=
          Nat.card_congr (MonoidHom.ofInjective ofSubtype_injective).toEquiv
      _ ≤ Nat.card H := Subgroup.card_le_of_le hsub
  have heq : Nat.card L = Nat.card H :=
    le_antisymm (hcard.trans hlow) (Nat.card_le_card_of_surjective f hf)
  obtain ⟨e⟩ := Finite.card_eq.1 heq
  have hinj : Function.Injective f := (Finite.injective_iff_surjective_of_equiv e).2 hf
  have : f ⟨g, hg⟩ = f 1 := Subtype.ext (by simp [f, h1])
  exact congrArg Subtype.val (hinj this)

lemma phi_injective : Function.Injective phi := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨n, hn⟩ := mem_some_level g
  exact level_injective n hn (congrArg Subtype.val hg)

theorem exists_mulEquiv_SigmaPres_SigmaPerm' :
    ∃ e : SigmaPres ≃* SigmaPerm, ∀ i, e (PresentedGroup.of i) = sigmaGen i :=
  ⟨MulEquiv.ofBijective phi ⟨phi_injective, phi_surjective⟩, fun i => phi_sg i⟩

end CannonFloydParry.S6

open CannonFloydParry in
theorem solution :
    ∃ e : SigmaPres ≃* SigmaPerm, ∀ i, e (PresentedGroup.of i) = sigmaGen i := by
  exact S6.exists_mulEquiv_SigmaPres_SigmaPerm'
