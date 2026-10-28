-- Prove2me | solution 1 for CookSensitivity.ChvatalRank.integerHull_eq_of_bounded_matrix
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:39:47.46243+00:00
-- url     : https://prove2.me/submissions/63319d84-6ae1-4265-becc-7bdf49ce0a71

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix
open scoped Classical

/-! ### Section 1: Nonnegative combinations and tight kernels -/

def coneSpan {n : ℕ} (G : Set (Fin n → ℚ)) : Set (Fin n → ℚ) :=
  {x | ∃ (k : ℕ) (g : Fin k → (Fin n → ℚ)) (c : Fin k → ℚ),
    (∀ j, g j ∈ G) ∧ (∀ j, 0 ≤ c j) ∧ x = ∑ j, c j • g j}

lemma zero_mem_coneSpan {n : ℕ} (G : Set (Fin n → ℚ)) : (0 : Fin n → ℚ) ∈ coneSpan G :=
  ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
    by simp⟩

lemma smul_mem_coneSpan {n : ℕ} {G : Set (Fin n → ℚ)} {g : Fin n → ℚ} (hg : g ∈ G) {c : ℚ}
    (hc : 0 ≤ c) : c • g ∈ coneSpan G :=
  ⟨1, fun _ => g, fun _ => c, fun _ => hg, fun _ => hc, by simp⟩

lemma coneSpan_add_smul {n : ℕ} {G : Set (Fin n → ℚ)} {x y : Fin n → ℚ} (hx : x ∈ coneSpan G)
    (hy : y ∈ coneSpan G) {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a • x + b • y ∈ coneSpan G := by
  obtain ⟨k₁, g₁, c₁, hg₁, hc₁, rfl⟩ := hx
  obtain ⟨k₂, g₂, c₂, hg₂, hc₂, rfl⟩ := hy
  refine ⟨k₁ + k₂, Fin.append g₁ g₂, Fin.append (fun j => a * c₁ j) (fun j => b * c₂ j),
    ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [Fin.append_left, hg₁]
    · simp [Fin.append_right, hg₂]
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left]; exact mul_nonneg ha (hc₁ j)
    · simp only [Fin.append_right]; exact mul_nonneg hb (hc₂ j)
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.smul_sum, smul_smul]

lemma coneSpan_sum {n : ℕ} {G : Set (Fin n → ℚ)} :
    ∀ (k : ℕ) (p : Fin k → (Fin n → ℚ)), (∀ j, p j ∈ coneSpan G) → (∑ j, p j) ∈ coneSpan G := by
  intro k
  induction k with
  | zero =>
    intro p _
    simpa using zero_mem_coneSpan G
  | succ k ih =>
    intro p hp
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun j => p (Fin.castSucc j)) (fun j => hp (Fin.castSucc j))
    have h2 := hp (Fin.last k)
    have := coneSpan_add_smul h1 h2 zero_le_one zero_le_one
    simpa using this

def tightK {ι : Type*} [Fintype ι] {n : ℕ} (B : Matrix ι (Fin n) ℚ) (x : Fin n → ℚ) :
    Submodule ℚ (Fin n → ℚ) where
  carrier := {y | ∀ c, (B *ᵥ x) c = 0 → (B *ᵥ y) c = 0}
  add_mem' := by
    intro a b ha hb c hc
    rw [mulVec_add, Pi.add_apply, ha c hc, hb c hc, add_zero]
  zero_mem' := by
    intro c _
    simp
  smul_mem' := by
    intro r y hy c hc
    rw [mulVec_smul, Pi.smul_apply, hy c hc, smul_zero]

lemma mem_tightK {ι : Type*} [Fintype ι] {n : ℕ} {B : Matrix ι (Fin n) ℚ} {x y : Fin n → ℚ} :
    y ∈ tightK B x ↔ ∀ c, (B *ᵥ x) c = 0 → (B *ᵥ y) c = 0 := Iff.rfl

lemma self_mem_tightK {ι : Type*} [Fintype ι] {n : ℕ} {B : Matrix ι (Fin n) ℚ} {x : Fin n → ℚ} :
    x ∈ tightK B x := fun _ hc => hc

lemma tightK_le {ι : Type*} [Fintype ι] {n : ℕ} {B : Matrix ι (Fin n) ℚ} {x q : Fin n → ℚ}
    (hq : q ∈ tightK B x) : tightK B q ≤ tightK B x := by
  intro y hy c hc
  exact hy c (hq c hc)

lemma finrank_tightK_lt {ι : Type*} [Fintype ι] {n : ℕ} {B : Matrix ι (Fin n) ℚ} {x q : Fin n → ℚ}
    (hq : q ∈ tightK B x) (c : ι) (h1 : (B *ᵥ q) c = 0) (h2 : (B *ᵥ x) c ≠ 0) :
    Module.finrank ℚ (tightK B q) < Module.finrank ℚ (tightK B x) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (tightK_le hq) ?_
  intro heq
  have : x ∈ tightK B q := heq ▸ self_mem_tightK
  exact h2 (this c h1)

lemma exit_lemma {ι : Type*} [Fintype ι] {n : ℕ} (B : Matrix ι (Fin n) ℚ) (x v : Fin n → ℚ)
    (hx : ∀ c, (B *ᵥ x) c ≤ 0) (hv : v ∈ tightK B x) :
    (∀ c, (B *ᵥ v) c ≤ 0) ∨
      ∃ τ : ℚ, 0 < τ ∧ (∀ c, (B *ᵥ (x + τ • v)) c ≤ 0) ∧
        ∃ c, (B *ᵥ (x + τ • v)) c = 0 ∧ (B *ᵥ x) c ≠ 0 := by
  by_cases hbad : ∀ c, (B *ᵥ v) c ≤ 0
  · exact Or.inl hbad
  push Not at hbad
  right
  set bad := Finset.univ.filter (fun c => 0 < (B *ᵥ v) c) with hbadDef
  have hne : bad.Nonempty := by
    obtain ⟨c, hc⟩ := hbad
    exact ⟨c, by simp [bad, hc]⟩
  obtain ⟨c₀, hc₀, hmin⟩ :=
    Finset.exists_min_image bad (fun c => -(B *ᵥ x) c / (B *ᵥ v) c) hne
  have hvc₀ : 0 < (B *ᵥ v) c₀ := by simpa [bad] using hc₀
  have hxc₀ : (B *ᵥ x) c₀ < 0 := by
    rcases (hx c₀).lt_or_eq with h | h
    · exact h
    · exact absurd (hv c₀ h) hvc₀.ne'
  have hτ : 0 < -(B *ᵥ x) c₀ / (B *ᵥ v) c₀ := div_pos (by linarith) hvc₀
  refine ⟨-(B *ᵥ x) c₀ / (B *ᵥ v) c₀, hτ, ?_, c₀, ?_, hxc₀.ne⟩
  · intro c
    rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hc : 0 < (B *ᵥ v) c
    · have := hmin c (by simp [bad, hc])
      rw [le_div_iff₀ hc] at this
      linarith
    · push Not at hc
      nlinarith [hx c]
  · rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      div_mul_cancel₀ _ hvc₀.ne']
    ring

theorem cone_descent {ι : Type*} [Fintype ι] {n : ℕ} (B : Matrix ι (Fin n) ℚ)
    (hpt : ∀ y : Fin n → ℚ, (∀ c, (B *ᵥ y) c ≤ 0) → (∀ c, (B *ᵥ (-y)) c ≤ 0) → y = 0)
    (G : Set (Fin n → ℚ))
    (hbase : ∀ x, (∀ c, (B *ᵥ x) c ≤ 0) → Module.finrank ℚ (tightK B x) ≤ 1 →
      x ∈ coneSpan G) :
    ∀ x, (∀ c, (B *ᵥ x) c ≤ 0) → x ∈ coneSpan G := by
  intro x hx
  induction' hd : Module.finrank ℚ (tightK B x) using Nat.strong_induction_on with d ih
    generalizing x
  by_cases hd1 : d ≤ 1
  · exact hbase x hx (hd ▸ hd1)
  push Not at hd1
  obtain ⟨z, hzK, hzs⟩ : ∃ z ∈ tightK B x, z ∉ Submodule.span ℚ {x} := by
    by_contra hcon
    push Not at hcon
    have hle : tightK B x ≤ Submodule.span ℚ {x} := fun z hz => hcon z hz
    have h1 : Module.finrank ℚ (tightK B x) ≤ Module.finrank ℚ (Submodule.span ℚ {x}) :=
      Submodule.finrank_mono (R := ℚ) (M := Fin n → ℚ) hle
    have h2 := finrank_span_le_card (R := ℚ) ({x} : Set (Fin n → ℚ))
    simp at h2
    omega
  have key : ∀ z ∈ tightK B x, z ∉ Submodule.span ℚ {x} → (∀ c, (B *ᵥ z) c ≤ 0) →
      x ∈ coneSpan G := by
    intro z hzK hzs hzC
    have hnegK : -z ∈ tightK B x := (tightK B x).neg_mem hzK
    rcases exit_lemma B x (-z) hx hnegK with hnegC | ⟨τ₂, hτ₂, hx₂C, c₂, hc₂, hc₂'⟩
    · exfalso
      apply hzs
      rw [hpt z hzC hnegC]
      exact Submodule.zero_mem _
    have hx₂K : x + τ₂ • (-z) ∈ tightK B x :=
      (tightK B x).add_mem self_mem_tightK ((tightK B x).smul_mem _ hnegK)
    have hx₂lt : Module.finrank ℚ (tightK B (x + τ₂ • (-z))) < d :=
      hd ▸ finrank_tightK_lt hx₂K c₂ hc₂ hc₂'
    have hx₂cone := ih _ hx₂lt (x + τ₂ • (-z)) hx₂C rfl
    by_cases hzlt : Module.finrank ℚ (tightK B z) < d
    · have hzcone := ih _ hzlt z hzC rfl
      have : x = (1 : ℚ) • (x + τ₂ • (-z)) + τ₂ • z := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        ring
      rw [this]
      exact coneSpan_add_smul hx₂cone hzcone zero_le_one hτ₂.le
    · push Not at hzlt
      have hKeq : tightK B z = tightK B x :=
        Submodule.eq_of_le_of_finrank_le (tightK_le hzK) (hd ▸ hzlt)
      have hnx₂K : -(x + τ₂ • (-z)) ∈ tightK B z := hKeq ▸ (tightK B x).neg_mem hx₂K
      rcases exit_lemma B z (-(x + τ₂ • (-z))) hzC hnx₂K with
        hnx₂C | ⟨τ₃, hτ₃, hz₁C, c₃, hc₃, hc₃'⟩
      · have hx₂0 : x + τ₂ • (-z) = 0 := hpt _ hx₂C hnx₂C
        exfalso
        apply hzs
        have hxz : x = τ₂ • z := by
          have := congrArg (fun y => y + τ₂ • z) hx₂0
          simpa [add_assoc, ← smul_add] using this
        have : z = τ₂⁻¹ • x := by
          rw [hxz, smul_smul, inv_mul_cancel₀ hτ₂.ne', one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      · have hz₁K : z + τ₃ • -(x + τ₂ • (-z)) ∈ tightK B z :=
          (tightK B z).add_mem self_mem_tightK ((tightK B z).smul_mem _ hnx₂K)
        have hz₁lt : Module.finrank ℚ (tightK B (z + τ₃ • -(x + τ₂ • (-z)))) < d := by
          have := finrank_tightK_lt hz₁K c₃ hc₃ hc₃'
          rw [hKeq, hd] at this
          exact this
        have hz₁cone := ih _ hz₁lt _ hz₁C rfl
        have : x = (1 + τ₂ * τ₃) • (x + τ₂ • (-z)) + τ₂ • (z + τ₃ • -(x + τ₂ • (-z))) := by
          ext i
          simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
          ring
        rw [this]
        exact coneSpan_add_smul hx₂cone hz₁cone (by positivity) hτ₂.le
  rcases exit_lemma B x z hx hzK with hzC | ⟨τ₁, hτ₁, hx₁C, c₁, hc₁, hc₁'⟩
  · exact key z hzK hzs hzC
  have hnegK : -z ∈ tightK B x := (tightK B x).neg_mem hzK
  rcases exit_lemma B x (-z) hx hnegK with hnegC | ⟨τ₂, hτ₂, hx₂C, c₂, hc₂, hc₂'⟩
  · exact key (-z) hnegK (fun h => hzs (by simpa using (Submodule.span ℚ {x}).neg_mem h)) hnegC
  have hx₁K : x + τ₁ • z ∈ tightK B x :=
    (tightK B x).add_mem self_mem_tightK ((tightK B x).smul_mem _ hzK)
  have hx₂K : x + τ₂ • (-z) ∈ tightK B x :=
    (tightK B x).add_mem self_mem_tightK ((tightK B x).smul_mem _ hnegK)
  have hx₁lt : Module.finrank ℚ (tightK B (x + τ₁ • z)) < d :=
    hd ▸ finrank_tightK_lt hx₁K c₁ hc₁ hc₁'
  have hx₂lt : Module.finrank ℚ (tightK B (x + τ₂ • (-z))) < d :=
    hd ▸ finrank_tightK_lt hx₂K c₂ hc₂ hc₂'
  have hx₁cone := ih _ hx₁lt _ hx₁C rfl
  have hx₂cone := ih _ hx₂lt _ hx₂C rfl
  have hpos : 0 < τ₁ + τ₂ := by linarith
  have : x = (τ₂ / (τ₁ + τ₂)) • (x + τ₁ • z) + (τ₁ / (τ₁ + τ₂)) • (x + τ₂ • (-z)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    field_simp
    ring
  rw [this]
  exact coneSpan_add_smul hx₁cone hx₂cone (div_nonneg hτ₂.le hpos.le)
    (div_nonneg hτ₁.le hpos.le)

theorem coneSpan_linIndep {n : ℕ} (G : Set (Fin n → ℚ)) :
    ∀ (k : ℕ) (g : Fin k → (Fin n → ℚ)) (c : Fin k → ℚ), (∀ j, g j ∈ G) → (∀ j, 0 ≤ c j) →
      ∃ (k' : ℕ) (g' : Fin k' → (Fin n → ℚ)) (c' : Fin k' → ℚ),
        (∀ j, g' j ∈ G) ∧ (∀ j, 0 ≤ c' j) ∧ ∑ j, c j • g j = ∑ j, c' j • g' j ∧
          LinearIndependent ℚ g' := by
  intro k
  induction k with
  | zero =>
    intro g c hg hc
    exact ⟨0, g, c, hg, hc, rfl, linearIndependent_empty_type⟩
  | succ k ih =>
    intro g c hg hc
    by_cases hli : LinearIndependent ℚ g
    · exact ⟨_, g, c, hg, hc, rfl, hli⟩
    rw [Fintype.not_linearIndependent_iff] at hli
    obtain ⟨μ, hμ, i₀, hi₀⟩ := hli
    obtain ⟨μ, hμ, j₁, hj₁⟩ : ∃ μ : Fin (k+1) → ℚ, ∑ j, μ j • g j = 0 ∧ ∃ j, 0 < μ j := by
      rcases lt_or_gt_of_ne hi₀ with h | h
      · refine ⟨-μ, ?_, i₀, by rw [Pi.neg_apply]; linarith⟩
        simp [neg_smul, Finset.sum_neg_distrib, hμ]
      · exact ⟨μ, hμ, i₀, h⟩
    set pos := Finset.univ.filter (fun j => 0 < μ j) with hposDef
    have hne : pos.Nonempty := ⟨j₁, by simp [pos, hj₁]⟩
    obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image pos (fun j => c j / μ j) hne
    have hμj₀ : 0 < μ j₀ := by simpa [pos] using hj₀
    have ht : 0 ≤ c j₀ / μ j₀ := div_nonneg (hc j₀) hμj₀.le
    set c' : Fin (k+1) → ℚ := fun j => c j - (c j₀ / μ j₀) * μ j with hc'Def
    have hc' : ∀ j, 0 ≤ c' j := by
      intro j
      simp only [c']
      by_cases h : 0 < μ j
      · have := hmin j (by simp [pos, h])
        rw [le_div_iff₀ h] at this
        linarith
      · push Not at h
        nlinarith [mul_nonneg ht (neg_nonneg.mpr h), hc j]
    have hc'j₀ : c' j₀ = 0 := by
      simp only [c']
      field_simp
      ring
    have hsum : ∑ j, c j • g j = ∑ j, c' j • g j := by
      simp only [c', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμ,
        smul_zero, sub_zero]
    obtain ⟨k', g', c'', hg', hc'', heq, hli'⟩ :=
      ih (fun j => g (j₀.succAbove j)) (fun j => c' (j₀.succAbove j)) (fun j => hg _)
        (fun j => hc' _)
    refine ⟨k', g', c'', hg', hc'', ?_, hli'⟩
    rw [hsum, Fin.sum_univ_succAbove _ j₀, hc'j₀, zero_smul, zero_add, heq]

theorem coneSpan_exists_le {n : ℕ} {G : Set (Fin n → ℚ)} {x : Fin n → ℚ} (hx : x ∈ coneSpan G) :
    ∃ (k : ℕ) (g : Fin k → (Fin n → ℚ)) (c : Fin k → ℚ), k ≤ n ∧ (∀ j, g j ∈ G) ∧
      (∀ j, 0 ≤ c j) ∧ x = ∑ j, c j • g j := by
  obtain ⟨k, g, c, hg, hc, rfl⟩ := hx
  obtain ⟨k', g', c', hg', hc', heq, hli⟩ := coneSpan_linIndep G k g c hg hc
  refine ⟨k', g', c', ?_, hg', hc', heq⟩
  have := hli.fintype_card_le_finrank
  simpa using this

/-! ### Section 2: Cofactor bound and sign-cone decomposition -/

lemma natAbs_det_submatrix_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0) (k : ℕ)
    (f : Fin k → Fin m) (g : Fin k → Fin n) (hf : Function.Injective f)
    (hg : Function.Injective g) :
    (A.submatrix f g).det.natAbs ≤ maxSubdet A := by
  have key : ∀ (k' : ℕ) (f : Fin (k'+1) → Fin m) (g : Fin (k'+1) → Fin n),
      Function.Injective f → Function.Injective g →
      (A.submatrix f g).det.natAbs ≤ maxSubdet A := by
    intro k' f g hf hg
    have hm : k' + 1 ≤ m := by simpa using Fintype.card_le_of_injective f hf
    have hn : k' + 1 ≤ n := by simpa using Fintype.card_le_of_injective g hg
    have hk : k' < min m n := by omega
    unfold maxSubdet
    refine le_trans ?_ (Finset.le_sup (f := fun k : Fin (min m n) =>
      Finset.univ.sup fun f : Fin (k.val + 1) ↪ Fin m =>
        Finset.univ.sup fun g : Fin (k.val + 1) ↪ Fin n => (A.submatrix f g).det.natAbs)
      (Finset.mem_univ ⟨k', hk⟩))
    refine le_trans ?_ (Finset.le_sup (f := fun f : Fin (k' + 1) ↪ Fin m =>
      Finset.univ.sup fun g : Fin (k' + 1) ↪ Fin n => (A.submatrix f g).det.natAbs)
      (Finset.mem_univ ⟨f, hf⟩))
    exact Finset.le_sup (f := fun g : Fin (k' + 1) ↪ Fin n =>
      (A.submatrix (⟨f, hf⟩ : Fin (k'+1) ↪ Fin m) g).det.natAbs) (Finset.mem_univ ⟨g, hg⟩)
  cases k with
  | zero =>
    rw [Matrix.det_fin_zero, Int.natAbs_one]
    obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hA (Matrix.ext h)
    have := key 0 (fun _ => i) (fun _ => j) (fun (a b : Fin 1) _ => Subsingleton.elim a b)
      (fun (a b : Fin 1) _ => Subsingleton.elim a b)
    change (A.submatrix (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)).det.natAbs ≤ _ at this
    rw [Matrix.det_fin_one] at this
    simp only [Matrix.submatrix_apply] at this
    have h1 : 0 < (A i j).natAbs := Int.natAbs_pos.mpr hij
    omega
  | succ k' => exact key k' f g hf hg

def supK {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (T : Finset (Fin m)) (J : Finset (Fin n)) :
    Submodule ℚ (Fin n → ℚ) where
  carrier := {y | (∀ i ∈ T, ((A.map (Int.cast : ℤ → ℚ)) *ᵥ y) i = 0) ∧ ∀ j, j ∉ J → y j = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · rw [mulVec_add, Pi.add_apply, ha1 i hi, hb1 i hi, add_zero]
    · rw [Pi.add_apply, ha2 j hj, hb2 j hj, add_zero]
  zero_mem' := ⟨fun i _ => by simp, fun j _ => rfl⟩
  smul_mem' := by
    rintro r y ⟨hy1, hy2⟩
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · rw [mulVec_smul, Pi.smul_apply, hy1 i hi, smul_zero]
    · rw [Pi.smul_apply, hy2 j hj, smul_zero]

lemma mem_supK {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {T : Finset (Fin m)} {J : Finset (Fin n)}
    {y : Fin n → ℚ} : y ∈ supK A T J ↔
      (∀ i ∈ T, ((A.map (Int.cast : ℤ → ℚ)) *ᵥ y) i = 0) ∧ ∀ j, j ∉ J → y j = 0 := Iff.rfl

theorem exists_integral_small_in_supK {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0)
    (T : Finset (Fin m)) (J : Finset (Fin n)) (x : Fin n → ℚ) (hx : x ∈ supK A T J)
    (hx0 : x ≠ 0) (hdim : Module.finrank ℚ (supK A T J) = 1) :
    ∃ g : Fin n → ℚ, IsIntegral g ∧ g ∈ supK A T J ∧ g ≠ 0 ∧
      ∀ j, |g j| ≤ (maxSubdet A : ℚ) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  have hj₀J : j₀ ∈ J := by
    by_contra h
    exact hj₀ (hx.2 j₀ h)
  obtain ⟨r', hr'⟩ : ∃ r', J.card = r' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨j₀, hj₀J⟩)
  have hcardJ : Fintype.card J = r' + 1 := by simp [hr']
  let eqv : J ≃ Fin (r' + 1) := Fintype.equivFinOfCardEq hcardJ
  let e : Fin (r' + 1) → Fin n := fun a => (eqv.symm a).1
  have he : Function.Injective e := Subtype.val_injective.comp eqv.symm.injective
  have heJ : ∀ a, e a ∈ J := fun a => (eqv.symm a).2
  have hJe : ∀ j ∈ J, ∃ a, e a = j := fun j hj => ⟨eqv ⟨j, hj⟩, by simp [e]⟩
  let E : Matrix (Fin n) (Fin (r' + 1)) ℚ := Matrix.of fun j a => if e a = j then 1 else 0
  have hE1 : ∀ (y : Fin (r' + 1) → ℚ) a, (E *ᵥ y) (e a) = y a := by
    intro y a
    simp [E, Matrix.mulVec, dotProduct, he.eq_iff]
  have hE2 : ∀ (y : Fin (r' + 1) → ℚ) j, j ∉ J → (E *ᵥ y) j = 0 := by
    intro y j hj
    simp only [E, Matrix.mulVec, dotProduct, Matrix.of_apply]
    apply Finset.sum_eq_zero
    intro a _
    have : e a ≠ j := fun h => hj (h ▸ heJ a)
    simp [this]
  have hE3 : ∀ (y : Fin (r' + 1) → ℚ) i,
      ((A.map (Int.cast : ℤ → ℚ)) *ᵥ (E *ᵥ y)) i = ∑ a, (A i (e a) : ℚ) * y a := by
    intro y i
    simp only [E, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.map_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [mul_ite, ite_mul]
  have hEinj : Function.Injective (E.mulVecLin) := by
    intro y y' h
    funext a
    have := congrFun h (e a)
    simp only [Matrix.mulVecLin_apply] at this
    rwa [hE1, hE1] at this
  have hsumJ : ∀ f : Fin n → ℚ, (∀ j, j ∉ J → f j = 0) → ∑ j, f j = ∑ a, f (e a) := by
    intro f hf
    rw [← Finset.sum_subset (Finset.subset_univ J) (fun j _ hj => hf j hj),
      ← Finset.sum_coe_sort J, ← Equiv.sum_comp eqv.symm]
  let ρ : T → (Fin (r' + 1) → ℚ) := fun i a => (A i.1 (e a) : ℚ)
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range ρ)
  have hbfin : b.Finite := (Set.finite_range ρ).subset hbsub
  have : Fintype b := hbfin.fintype
  obtain ⟨rb, hrb⟩ : ∃ rb, Fintype.card b = rb := ⟨_, rfl⟩
  let ι : Fin rb ≃ b := (Fintype.equivFinOfCardEq hrb).symm
  have hpre : ∀ v : b, ∃ i : T, ρ i = v := fun v => hbsub v.2
  choose pre hpre using hpre
  let ρ' : Fin rb → Fin m := fun a => (pre (ι a)).1
  let rowv : Fin rb → (Fin (r' + 1) → ℚ) := fun a => ((ι a : b) : Fin (r' + 1) → ℚ)
  have hrowv : ∀ a c, rowv a c = (A (ρ' a) (e c) : ℚ) := by
    intro a c
    simp only [rowv, ρ']
    rw [← hpre (ι a)]
  have hrowv_li : LinearIndependent ℚ rowv := hbli.comp ι ι.injective
  have hρ'T : ∀ a, ρ' a ∈ T := fun a => (pre (ι a)).2
  have hρ'inj : Function.Injective ρ' := by
    intro a a' h
    apply hrowv_li.injective
    funext c
    rw [hrowv, hrowv, h]
  have hrange : Set.range rowv = b := by
    have : rowv = Subtype.val ∘ ι := rfl
    rw [this, EquivLike.range_comp, Subtype.range_coe]
  have hspan_rowv : Submodule.span ℚ (Set.range rowv) = Submodule.span ℚ (Set.range ρ) := by
    rw [hrange, hbspan]
  have hfinrank_span : Module.finrank ℚ (Submodule.span ℚ (Set.range rowv)) = rb := by
    rw [finrank_span_eq_card hrowv_li, Fintype.card_fin]
  let N : Matrix (Fin rb) (Fin (r' + 1)) ℚ := Matrix.of fun a c => (A (ρ' a) (e c) : ℚ)
  have hNrow : ∀ a, N a = rowv a := by
    intro a
    funext c
    simp [N, hrowv]
  have hkerN : ∀ y : Fin (r' + 1) → ℚ, N *ᵥ y = 0 → E *ᵥ y ∈ supK A T J := by
    intro y hy
    refine ⟨fun i hi => ?_, fun j hj => hE2 y j hj⟩
    rw [hE3]
    have hmem : ρ ⟨i, hi⟩ ∈ Submodule.span ℚ (Set.range rowv) := by
      rw [hspan_rowv]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨cf, hcf⟩ := hmem
    have h1 : ∀ a, (A i (e a) : ℚ) = ∑ a', cf a' * rowv a' a := by
      intro a
      have := congrFun hcf a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
    simp_rw [h1, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a' _
    have : (N *ᵥ y) a' = 0 := by rw [hy]; rfl
    simp only [Matrix.mulVec, dotProduct, hNrow] at this
    simp only [mul_assoc]
    rw [← Finset.mul_sum, this, mul_zero]
  let xJ : Fin (r' + 1) → ℚ := fun a => x (e a)
  have hxJ : N *ᵥ xJ = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, N, Matrix.of_apply, Pi.zero_apply, xJ]
    have := hx.1 (ρ' a) (hρ'T a)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at this
    rw [hsumJ (fun j => (A (ρ' a) j : ℚ) * x j) (fun j hj => by rw [hx.2 j hj, mul_zero])] at this
    exact this
  have hxJ0 : xJ ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := hJe j₀ hj₀J
    have := congrFun h a
    simp only [xJ, Pi.zero_apply, ha] at this
    exact hj₀ this
  have hrb : rb = r' := by
    have hrn : N.rank = rb := by
      rw [Matrix.rank_eq_finrank_span_row]
      have : Set.range N.row = Set.range rowv := by
        show Set.range N = _
        rw [show N = rowv from funext hNrow]
      rw [this, hfinrank_span]
    have hrk := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fin_fun] at hrk
    have hker_le : Module.finrank ℚ (LinearMap.ker N.mulVecLin) ≤
        Module.finrank ℚ (supK A T J) := by
      let f : LinearMap.ker N.mulVecLin →ₗ[ℚ] supK A T J :=
        LinearMap.codRestrict (supK A T J) (E.mulVecLin.domRestrict (LinearMap.ker N.mulVecLin))
          (fun y => hkerN y.1 (LinearMap.mem_ker.mp y.2))
      refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
      intro y y' h
      apply Subtype.ext
      apply hEinj
      have := congrArg Subtype.val h
      exact this
    have hker_ge : 0 < Module.finrank ℚ (LinearMap.ker N.mulVecLin) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨⟨xJ, LinearMap.mem_ker.mpr hxJ⟩, ?_⟩
      intro h
      exact hxJ0 (congrArg Subtype.val h)
    unfold Matrix.rank at hrn
    omega
  subst hrb
  let M : Matrix (Fin (rb + 1)) (Fin (rb + 1)) ℤ :=
    Matrix.of fun a c => if h : a.val < rb then A (ρ' ⟨a.val, h⟩) (e c) else 0
  have hMcast : ∀ (a : Fin rb) c, M (Fin.castSucc a) c = A (ρ' a) (e c) := by
    intro a c
    simp [M]
  have hMlast : ∀ c, M (Fin.last rb) c = 0 := by
    intro c
    simp [M]
  let g' : Fin (rb + 1) → ℤ := fun a => M.adjugate a (Fin.last rb)
  have hMg' : ∀ a, ∑ c, M a c * g' c = 0 := by
    intro a
    have := Matrix.mul_adjugate M
    rw [Matrix.det_eq_zero_of_row_eq_zero (Fin.last rb) hMlast, zero_smul] at this
    have := congrFun (congrFun this a) (Fin.last rb)
    simpa [Matrix.mul_apply, g'] using this
  have hNg' : N *ᵥ (fun c => (g' c : ℚ)) = 0 := by
    funext a
    have := hMg' (Fin.castSucc a)
    simp only [hMcast] at this
    simp only [Matrix.mulVec, dotProduct, N, Matrix.of_apply, Pi.zero_apply]
    exact_mod_cast this
  let Mq : Matrix (Fin (rb + 1)) (Fin (rb + 1)) ℚ := M.map (Int.cast : ℤ → ℚ)
  have hMqcast : ∀ a : Fin rb, Mq (Fin.castSucc a) = rowv a := by
    intro a
    funext c
    simp [Mq, hMcast, hrowv]
  obtain ⟨a₀, ha₀⟩ : ∃ a, Pi.single a (1 : ℚ) ∉ Submodule.span ℚ (Set.range rowv) := by
    by_contra h
    push Not at h
    have htop : (⊤ : Submodule ℚ (Fin (rb + 1) → ℚ)) ≤ Submodule.span ℚ (Set.range rowv) := by
      rw [← (Pi.basisFun ℚ (Fin (rb + 1))).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      rw [Pi.basisFun_apply]
      exact h a
    have := Submodule.finrank_mono (R := ℚ) (M := Fin (rb + 1) → ℚ) htop
    rw [finrank_top, Module.finrank_fin_fun, hfinrank_span] at this
    omega
  have hdet : (Mq.updateRow (Fin.last rb) (Pi.single a₀ 1)).det ≠ 0 := by
    have hrows : (Mq.updateRow (Fin.last rb) (Pi.single a₀ 1)) =
        Fin.snoc rowv (Pi.single a₀ 1) := by
      funext r
      refine Fin.lastCases ?_ (fun r' => ?_) r
      · rw [Matrix.updateRow_self, Fin.snoc_last]
      · rw [Matrix.updateRow_ne (Fin.castSucc_lt_last r').ne, Fin.snoc_castSucc, hMqcast]
    have hli : LinearIndependent ℚ (Mq.updateRow (Fin.last rb) (Pi.single a₀ 1)).row := by
      show LinearIndependent ℚ (Mq.updateRow (Fin.last rb) (Pi.single a₀ 1))
      rw [hrows]
      exact linearIndependent_finSnoc.mpr ⟨hrowv_li, ha₀⟩
    rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero] at hli
    exact hli
  have hg'a₀ : g' a₀ ≠ 0 := by
    intro h
    apply hdet
    rw [← Matrix.adjugate_apply]
    have hmap := RingHom.map_adjugate (Int.castRingHom ℚ) M
    have : Mq = (Int.castRingHom ℚ).mapMatrix M := by
      simp [Mq, RingHom.mapMatrix_apply]
    rw [this, ← hmap, RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [g'] at h
    rw [h]
    simp
  have hg'bound : ∀ a, |(g' a : ℚ)| ≤ (maxSubdet A : ℚ) := by
    intro a
    have h1 : (g' a).natAbs ≤ maxSubdet A := by
      simp only [g']
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Int.natAbs_mul, Int.natAbs_pow,
        Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
      have hsub : M.submatrix (Fin.last rb).succAbove a.succAbove =
          A.submatrix ρ' (e ∘ a.succAbove) := by
        ext a' c'
        simp [Matrix.submatrix_apply, Fin.succAbove_last, hMcast]
      rw [hsub]
      exact natAbs_det_submatrix_le A hA rb ρ' (e ∘ a.succAbove) hρ'inj
        (he.comp Fin.succAbove_right_injective)
    have h2 : ((g' a).natAbs : ℚ) ≤ (maxSubdet A : ℚ) := by exact_mod_cast h1
    rwa [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs] at h2
  refine ⟨E *ᵥ (fun c => (g' c : ℚ)), ?_, hkerN _ hNg', ?_, ?_⟩
  · intro j
    refine ⟨∑ a, if e a = j then g' a else 0, ?_⟩
    simp only [E, Matrix.mulVec, dotProduct, Matrix.of_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  · intro h
    have := congrFun h (e a₀)
    rw [hE1, Pi.zero_apply] at this
    exact hg'a₀ (by exact_mod_cast this)
  · intro j
    by_cases hj : j ∈ J
    · obtain ⟨a, rfl⟩ := hJe j hj
      rw [hE1]
      exact hg'bound a
    · rw [hE2 _ j hj, abs_zero]
      exact Nat.cast_nonneg _

lemma supNorm_le_iff {k : ℕ} {x : Fin k → ℚ} {a : ℚ} :
    supNorm x ≤ a ↔ 0 ≤ a ∧ ∀ i, |x i| ≤ a := by
  unfold supNorm
  rw [Finset.fold_max_le]
  simp

lemma abs_le_supNorm {k : ℕ} (x : Fin k → ℚ) (i : Fin k) : |x i| ≤ supNorm x := by
  unfold supNorm
  rw [Finset.le_fold_max]
  exact Or.inr ⟨i, Finset.mem_univ _, le_rfl⟩

lemma supNorm_nonneg {k : ℕ} (x : Fin k → ℚ) : 0 ≤ supNorm x := by
  unfold supNorm
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

lemma supNorm_neg {k : ℕ} (x : Fin k → ℚ) : supNorm (-x) = supNorm x := by
  simp [supNorm, abs_neg]

lemma supNorm_add_le {k : ℕ} (x y : Fin k → ℚ) : supNorm (x + y) ≤ supNorm x + supNorm y := by
  rw [supNorm_le_iff]
  refine ⟨add_nonneg (supNorm_nonneg x) (supNorm_nonneg y), fun i => ?_⟩
  rw [Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (abs_le_supNorm x i) (abs_le_supNorm y i))

lemma supNorm_sum_smul_le {n k : ℕ} (c : Fin k → ℚ) (g : Fin k → (Fin n → ℚ)) (D : ℚ)
    (hc : ∀ j, 0 ≤ c j) (hg : ∀ j, supNorm (g j) ≤ D) :
    supNorm (∑ j, c j • g j) ≤ (∑ j, c j) * D := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [supNorm_le_iff]
    simp
  have hD : 0 ≤ D := (supNorm_nonneg _).trans (hg ⟨0, hk⟩)
  rw [supNorm_le_iff]
  refine ⟨mul_nonneg (Finset.sum_nonneg fun j _ => hc j) hD, fun i => ?_⟩
  rw [Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hc j)]
  exact mul_le_mul_of_nonneg_left ((abs_le_supNorm _ i).trans (hg j)) (hc j)

lemma isIntegral_add {n : ℕ} {x y : Fin n → ℚ} (hx : IsIntegral x) (hy : IsIntegral y) :
    IsIntegral (x + y) := by
  intro i
  obtain ⟨a, ha⟩ := hx i
  obtain ⟨b, hb⟩ := hy i
  exact ⟨a + b, by simp [ha, hb]⟩

lemma isIntegral_neg {n : ℕ} {x : Fin n → ℚ} (hx : IsIntegral x) : IsIntegral (-x) := by
  intro i
  obtain ⟨a, ha⟩ := hx i
  exact ⟨-a, by simp [ha]⟩

lemma isIntegral_sub {n : ℕ} {x y : Fin n → ℚ} (hx : IsIntegral x) (hy : IsIntegral y) :
    IsIntegral (x - y) := by
  rw [sub_eq_add_neg]
  exact isIntegral_add hx (isIntegral_neg hy)

lemma isIntegral_zero {n : ℕ} : IsIntegral (0 : Fin n → ℚ) := fun _ => ⟨0, by simp⟩

lemma isIntegral_intSmul {n : ℕ} (z : ℤ) {x : Fin n → ℚ} (hx : IsIntegral x) :
    IsIntegral ((z : ℚ) • x) := by
  intro i
  obtain ⟨a, ha⟩ := hx i
  exact ⟨z * a, by simp [ha]⟩

lemma isIntegral_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ℚ))
    (hf : ∀ j ∈ s, IsIntegral (f j)) : IsIntegral (∑ j ∈ s, f j) := by
  induction s using Finset.induction_on with
  | empty => simpa using isIntegral_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntegral_add (hf a (Finset.mem_insert_self a s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma mulVec_integral {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {g : Fin n → ℚ}
    (hg : IsIntegral g) (i : Fin m) :
    ∃ z : ℤ, ((A.map (Int.cast : ℤ → ℚ)) *ᵥ g) i = z := by
  choose k hk using hg
  refine ⟨∑ j, A i j * k j, ?_⟩
  simp [Matrix.mulVec, dotProduct, hk]

lemma mulVec_sum_smul {m n k : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (f : Fin k → ℚ)
    (g : Fin k → (Fin n → ℚ)) (i : Fin m) :
    (M *ᵥ (∑ j, f j • g j)) i = ∑ j, f j * (M *ᵥ g j) i := by
  have : M *ᵥ (∑ j, f j • g j) = ∑ j, f j • (M *ᵥ g j) := by
    rw [← Matrix.mulVecLin_apply, map_sum]
    simp
  rw [this, Finset.sum_apply]
  simp

lemma dot_sum_smul {n k : ℕ} (w : Fin n → ℚ) (f : Fin k → ℚ) (g : Fin k → (Fin n → ℚ)) :
    w ⬝ᵥ (∑ j, f j • g j) = ∑ j, f j * (w ⬝ᵥ g j) := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

def coneMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin m → ℚ) (σ : Fin n → ℚ) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℚ :=
  Matrix.of fun c j' =>
    Sum.elim (fun i => s i * (A i j' : ℚ)) (fun j => if j' = j then σ j else 0) c

lemma coneMat_mulVec_inl {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin m → ℚ)
    (σ : Fin n → ℚ) (y : Fin n → ℚ) (i : Fin m) :
    (coneMat A s σ *ᵥ y) (Sum.inl i) = s i * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ y) i := by
  simp [coneMat, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma coneMat_mulVec_inr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin m → ℚ)
    (σ : Fin n → ℚ) (y : Fin n → ℚ) (j : Fin n) :
    (coneMat A s σ *ᵥ y) (Sum.inr j) = σ j * y j := by
  simp [coneMat, Matrix.mulVec, dotProduct, ite_mul]

lemma coneMat_pointed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin m → ℚ)
    (σ : Fin n → ℚ) (hσ : ∀ j, σ j ≠ 0) (y : Fin n → ℚ)
    (h1 : ∀ c, (coneMat A s σ *ᵥ y) c ≤ 0) (h2 : ∀ c, (coneMat A s σ *ᵥ (-y)) c ≤ 0) :
    y = 0 := by
  funext j
  have a1 := h1 (Sum.inr j)
  have a2 := h2 (Sum.inr j)
  rw [coneMat_mulVec_inr] at a1 a2
  rw [Pi.neg_apply, mul_neg] at a2
  have : σ j * y j = 0 := le_antisymm a1 (by linarith)
  rw [Pi.zero_apply]
  exact (mul_eq_zero.mp this).resolve_left (hσ j)

lemma tightK_coneMat_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin m → ℚ)
    (σ : Fin n → ℚ) (hs : ∀ i, s i ≠ 0) (hσ : ∀ j, σ j ≠ 0) (x : Fin n → ℚ) :
    tightK (coneMat A s σ) x =
      supK A (Finset.univ.filter fun i => ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i = 0)
        (Finset.univ.filter fun j => x j ≠ 0) := by
  ext y
  rw [mem_tightK, mem_supK]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have hi' : ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i = 0 := by simpa using hi
      have := h (Sum.inl i) (by rw [coneMat_mulVec_inl, hi', mul_zero])
      rw [coneMat_mulVec_inl] at this
      exact (mul_eq_zero.mp this).resolve_left (hs i)
    · have hj' : x j = 0 := by simpa using hj
      have := h (Sum.inr j) (by rw [coneMat_mulVec_inr, hj', mul_zero])
      rw [coneMat_mulVec_inr] at this
      exact (mul_eq_zero.mp this).resolve_left (hσ j)
  · rintro ⟨h1, h2⟩ c hc
    rcases c with i | j
    · rw [coneMat_mulVec_inl] at hc ⊢
      have := (mul_eq_zero.mp hc).resolve_left (hs i)
      rw [h1 i (by simpa using this), mul_zero]
    · rw [coneMat_mulVec_inr] at hc ⊢
      have := (mul_eq_zero.mp hc).resolve_left (hσ j)
      rw [h2 j (by simpa using this), mul_zero]

def coneGens {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin m → ℚ) (σ : Fin n → ℚ) :
    Set (Fin n → ℚ) :=
  {g | IsIntegral g ∧ (∀ c, (coneMat A s σ *ᵥ g) c ≤ 0) ∧ supNorm g ≤ (maxSubdet A : ℚ)}

lemma coneMat_base {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0) (s : Fin m → ℚ)
    (σ : Fin n → ℚ) (hs : ∀ i, s i ≠ 0) (hσ : ∀ j, σ j ≠ 0) (x : Fin n → ℚ)
    (hx : ∀ c, (coneMat A s σ *ᵥ x) c ≤ 0)
    (hdim : Module.finrank ℚ (tightK (coneMat A s σ) x) ≤ 1) :
    x ∈ coneSpan (coneGens A s σ) := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem_coneSpan _
  set B := coneMat A s σ with hB
  have hxK : x ∈ tightK B x := self_mem_tightK
  have hpos : 0 < Module.finrank ℚ (tightK B x) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨x, hxK⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  have hdim1 : Module.finrank ℚ (tightK B x) = 1 := by omega
  have hdimK : Module.finrank ℚ (supK A
      (Finset.univ.filter fun i => ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i = 0)
      (Finset.univ.filter fun j => x j ≠ 0)) = 1 := by
    rw [← tightK_coneMat_eq A s σ hs hσ x]; exact hdim1
  have hxK' : x ∈ supK A (Finset.univ.filter fun i => ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i = 0)
      (Finset.univ.filter fun j => x j ≠ 0) := by
    rw [← tightK_coneMat_eq A s σ hs hσ x]; exact hxK
  obtain ⟨g, hgI, hgK, hg0, hgb⟩ :=
    exists_integral_small_in_supK A hA _ _ x hxK' hx0 hdimK
  rw [← tightK_coneMat_eq A s σ hs hσ x] at hgK
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hxK⟩ : tightK B x)
    (fun h => hx0 (congrArg Subtype.val h))).mp hdim1 ⟨g, hgK⟩
  have hcx : c • x = g := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcx
    exact hg0 hcx.symm
  have hBg : ∀ c', (B *ᵥ g) c' = c * (B *ᵥ x) c' := by
    intro c'
    rw [← hcx, mulVec_smul, Pi.smul_apply, smul_eq_mul]
  rcases lt_or_gt_of_ne hc0 with hneg | hpos'
  · have hmem : -g ∈ coneGens A s σ := by
      refine ⟨isIntegral_neg hgI, fun c' => ?_, ?_⟩
      · rw [mulVec_neg, Pi.neg_apply, hBg]
        nlinarith [hx c']
      · rw [supNorm_le_iff]
        exact ⟨Nat.cast_nonneg _, fun j => by rw [Pi.neg_apply, abs_neg]; exact hgb j⟩
    have : x = (-c)⁻¹ • (-g) := by
      rw [← hcx]
      ext i
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      field_simp
    rw [this]
    exact smul_mem_coneSpan hmem (inv_nonneg.mpr (by linarith))
  · have hmem : g ∈ coneGens A s σ := by
      refine ⟨hgI, fun c' => ?_, ?_⟩
      · rw [hBg]
        nlinarith [hx c']
      · rw [supNorm_le_iff]
        exact ⟨Nat.cast_nonneg _, hgb⟩
    have : x = c⁻¹ • g := by
      rw [← hcx, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact smul_mem_coneSpan hmem (inv_nonneg.mpr hpos'.le)

theorem decomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0) (s : Fin m → ℚ)
    (hs : ∀ i, s i ≠ 0) (x : Fin n → ℚ)
    (hx : ∀ i, s i * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i ≤ 0) :
    ∃ (k : ℕ) (g : Fin k → (Fin n → ℚ)) (c : Fin k → ℚ), k ≤ n ∧ (∀ j, IsIntegral (g j)) ∧
      (∀ j i, s i * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ g j) i ≤ 0) ∧
      (∀ j, supNorm (g j) ≤ (maxSubdet A : ℚ)) ∧ (∀ j, 0 ≤ c j) ∧ x = ∑ j, c j • g j := by
  let σ : Fin n → ℚ := fun j => if 0 ≤ x j then -1 else 1
  have hσ : ∀ j, σ j ≠ 0 := by
    intro j
    simp only [σ]
    split_ifs <;> norm_num
  have hxC : ∀ c, (coneMat A s σ *ᵥ x) c ≤ 0 := by
    rintro (i | j)
    · rw [coneMat_mulVec_inl]; exact hx i
    · rw [coneMat_mulVec_inr]
      simp only [σ]
      split_ifs with h
      · linarith
      · push Not at h; linarith
  have hmem := cone_descent (coneMat A s σ) (coneMat_pointed A s σ hσ) (coneGens A s σ)
    (coneMat_base A hA s σ hs hσ) x hxC
  obtain ⟨k, g, c, hk, hg, hc, hsum⟩ := coneSpan_exists_le hmem
  refine ⟨k, g, c, hk, fun j => (hg j).1, fun j i => ?_, fun j => (hg j).2.2, hc, hsum⟩
  have := (hg j).2.1 (Sum.inl i)
  rwa [coneMat_mulVec_inl] at this

/-! ### Section 3: Existence of integer optima and small improving vectors -/

lemma exists_ip_optimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (w : Fin n → ℚ)
    (hint : ∃ x ∈ polyhedron A b, IsIntegral x)
    (hbd : ∃ M : ℚ, ∀ y ∈ polyhedron A b, IsIntegral y → w ⬝ᵥ y ≤ M) :
    ∃ z, IsIPOptimal A b w z := by
  obtain ⟨M, hM⟩ := hbd
  set D : ℤ := ∏ i, ((w i).den : ℤ) with hD
  have hDpos : (0 : ℚ) < D := by
    rw [hD]
    push_cast
    exact Finset.prod_pos (fun i _ => by exact_mod_cast (w i).den_pos)
  have hDw : ∀ i, ∃ z : ℤ, (D : ℚ) * w i = z := by
    intro i
    obtain ⟨D', hD'⟩ := Finset.dvd_prod_of_mem (fun i => ((w i).den : ℤ)) (Finset.mem_univ i)
    refine ⟨D' * (w i).num, ?_⟩
    have hD'' : (D : ℚ) = ((w i).den : ℚ) * (D' : ℚ) := by
      rw [hD]
      exact_mod_cast hD'
    rw [hD'', mul_comm ((w i).den : ℚ), mul_assoc, mul_comm ((w i).den : ℚ),
      Rat.mul_den_eq_num]
    push_cast
    ring
  choose dw hdw using hDw
  have hval : ∀ y : Fin n → ℚ, IsIntegral y → ∃ z : ℤ, (D : ℚ) * (w ⬝ᵥ y) = z := by
    intro y hy
    choose ky hky using hy
    refine ⟨∑ i, dw i * ky i, ?_⟩
    simp only [dotProduct, Finset.mul_sum, ← mul_assoc, hdw, hky]
    push_cast
    rfl
  let P : ℤ → Prop := fun z => ∃ y ∈ polyhedron A b, IsIntegral y ∧ (D : ℚ) * (w ⬝ᵥ y) = z
  have Hinh : ∃ z, P z := by
    obtain ⟨x, hxP, hxI⟩ := hint
    obtain ⟨z, hz⟩ := hval x hxI
    exact ⟨z, x, hxP, hxI, hz⟩
  have Hbdd : ∃ bnd : ℤ, ∀ z, P z → z ≤ bnd := by
    refine ⟨⌈(D : ℚ) * M⌉, ?_⟩
    rintro z ⟨y, hyP, hyI, hyz⟩
    have h1 : (z : ℚ) ≤ (D : ℚ) * M := by
      rw [← hyz]
      exact mul_le_mul_of_nonneg_left (hM y hyP hyI) hDpos.le
    have h2 := Int.le_ceil ((D : ℚ) * M)
    exact_mod_cast h1.trans h2
  obtain ⟨ub, ⟨z, hzP, hzI, hzv⟩, hub⟩ := Int.exists_greatest_of_bdd Hbdd Hinh
  refine ⟨z, hzI, hzP, fun y hy hyI => ?_⟩
  obtain ⟨zy, hzy⟩ := hval y hyI
  have h1 : zy ≤ ub := hub zy ⟨y, hy, hyI, hzy⟩
  have h2 : (D : ℚ) * (w ⬝ᵥ y) ≤ (D : ℚ) * (w ⬝ᵥ z) := by
    rw [hzy, hzv]
    exact_mod_cast h1
  exact le_of_mul_le_mul_left h2 hDpos

lemma polyhedron_zero {m n : ℕ} (b : Fin m → ℚ) (x : Fin n → ℚ)
    (hx : x ∈ polyhedron (0 : Matrix (Fin m) (Fin n) ℤ) b) :
    polyhedron (0 : Matrix (Fin m) (Fin n) ℤ) b = Set.univ := by
  have h0 : (0 : Matrix (Fin m) (Fin n) ℤ).map (Int.cast : ℤ → ℚ) = 0 :=
    Matrix.map_zero _ Int.cast_zero
  simp only [polyhedron, Set.mem_ofPred_eq, h0, Matrix.zero_mulVec] at hx
  ext y
  simp only [polyhedron, Set.mem_ofPred_eq, h0, Matrix.zero_mulVec, Set.mem_univ, iff_true]
  exact hx

theorem improving_vector_small_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0)
    (b : Fin m → ℚ) (w : Fin n → ℚ)
    (z : Fin n → ℚ) (hz : IsIntegral z) (hzP : z ∈ polyhedron A b) :
    IsIPOptimal A b w z ∨
      ∃ zbar, IsIntegral zbar ∧ zbar ∈ polyhedron A b ∧
        supNorm (z - zbar) ≤ (n : ℚ) * (maxSubdet A : ℚ) ∧ w ⬝ᵥ zbar > w ⬝ᵥ z := by
  by_cases hopt : IsIPOptimal A b w z
  · exact Or.inl hopt
  right
  obtain ⟨y, hyP, hyI, hwy⟩ : ∃ y ∈ polyhedron A b, IsIntegral y ∧ w ⬝ᵥ z < w ⬝ᵥ y := by
    by_contra h
    push Not at h
    exact hopt ⟨hz, hzP, fun y hy hyI => h y hy hyI⟩
  set Am := A.map (Int.cast : ℤ → ℚ) with hAm
  set d := y - z with hd
  let s : Fin m → ℚ := fun i => if 0 ≤ (Am *ᵥ d) i then -1 else 1
  have hs : ∀ i, s i ≠ 0 := by
    intro i
    simp only [s]
    split_ifs <;> norm_num
  have hdC : ∀ i, s i * (Am *ᵥ d) i ≤ 0 := by
    intro i
    simp only [s]
    split_ifs with h
    · linarith
    · push Not at h; linarith
  obtain ⟨k, g, c, hk, hgI, hgC, hgN, hc, hsum⟩ := decomposition A hA s hs d hdC
  have hpos : ∀ i, 0 ≤ (Am *ᵥ d) i → ∀ j, 0 ≤ (Am *ᵥ g j) i := by
    intro i hi j
    have := hgC j i
    simp only [s, if_pos hi] at this
    linarith
  have hneg : ∀ i, (Am *ᵥ d) i < 0 → ∀ j, (Am *ᵥ g j) i ≤ 0 := by
    intro i hi j
    have := hgC j i
    simp only [s, if_neg (not_le.mpr hi)] at this
    linarith
  set f : Fin k → ℚ := fun j => (⌊c j⌋ : ℚ) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by
    simp only [f]
    exact_mod_cast Int.floor_nonneg.mpr (hc j)
  have hfle : ∀ j, f j ≤ c j := fun j => Int.floor_le _
  have hfrac : ∀ j, c j - f j ≤ 1 := fun j => by
    have := Int.lt_floor_add_one (c j)
    simp only [f]
    linarith
  set v := ∑ j, f j • g j with hv
  have hvI : IsIntegral v := isIntegral_sum _ _ (fun j _ => isIntegral_intSmul _ (hgI j))
  set u := d - v with hu
  have huI : IsIntegral u := isIntegral_sub (isIntegral_sub hyI hz) hvI
  have hdu : u = ∑ j, (c j - f j) • g j := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hsum, ← hv]
  have hAv : ∀ i, (Am *ᵥ v) i = ∑ j, f j * (Am *ᵥ g j) i := fun i => mulVec_sum_smul Am f g i
  have hAd : ∀ i, (Am *ᵥ d) i = ∑ j, c j * (Am *ᵥ g j) i := fun i => by
    rw [hsum]
    exact mulVec_sum_smul Am c g i
  have hAd' : ∀ i, (Am *ᵥ d) i = (Am *ᵥ y) i - (Am *ᵥ z) i := fun i => by
    rw [hd, mulVec_sub]
    rfl
  have hbound : supNorm u ≤ (n : ℚ) * (maxSubdet A : ℚ) := by
    rw [hdu]
    refine (supNorm_sum_smul_le _ _ _ (fun j => by linarith [hfle j]) hgN).trans ?_
    have hle : ∑ j, (c j - f j) ≤ (k : ℚ) := by
      calc ∑ j, (c j - f j) ≤ ∑ _j : Fin k, (1 : ℚ) := Finset.sum_le_sum fun j _ => hfrac j
        _ = k := by simp
    have hk' : (k : ℚ) ≤ n := by exact_mod_cast hk
    exact mul_le_mul_of_nonneg_right (hle.trans hk') (Nat.cast_nonneg _)
  have hzu : z + u ∈ polyhedron A b := by
    show Am *ᵥ (z + u) ≤ b
    intro i
    have hAzu : (Am *ᵥ (z + u)) i = (Am *ᵥ y) i - ∑ j, f j * (Am *ᵥ g j) i := by
      rw [hu, hd, mulVec_add, mulVec_sub, mulVec_sub, Pi.add_apply, Pi.sub_apply, Pi.sub_apply,
        hAv]
      ring
    rw [hAzu]
    by_cases hi : 0 ≤ (Am *ᵥ d) i
    · have h1 : 0 ≤ ∑ j, f j * (Am *ᵥ g j) i :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hf0 j) (hpos i hi j)
      have h2 : (Am *ᵥ y) i ≤ b i := hyP i
      linarith
    · push Not at hi
      have h1 : ∑ j, (c j - f j) * (Am *ᵥ g j) i ≤ 0 :=
        Finset.sum_nonpos fun j _ =>
          mul_nonpos_iff.mpr (Or.inl ⟨by linarith [hfle j], hneg i hi j⟩)
      have h2 : (Am *ᵥ z) i ≤ b i := hzP i
      have h3 := hAd i
      rw [hAd'] at h3
      simp only [sub_mul, Finset.sum_sub_distrib] at h1
      linarith
  have hwd' : w ⬝ᵥ d = w ⬝ᵥ y - w ⬝ᵥ z := by rw [hd, dotProduct_sub]
  have hwv : w ⬝ᵥ v = ∑ j, f j * (w ⬝ᵥ g j) := by rw [hv, dot_sum_smul]
  have hwzu : w ⬝ᵥ (z + u) = w ⬝ᵥ y - ∑ j, f j * (w ⬝ᵥ g j) := by
    rw [hu, dotProduct_add, dotProduct_sub, hwd', hwv]
    ring
  by_cases hwu : w ⬝ᵥ z < w ⬝ᵥ (z + u)
  · refine ⟨z + u, isIntegral_add hz huI, hzu, ?_, hwu⟩
    have : z - (z + u) = -u := by abel
    rw [this, supNorm_neg]
    exact hbound
  · push Not at hwu
    rw [hwzu] at hwu
    have hsumpos : ∑ _j : Fin k, (0 : ℚ) < ∑ j, f j * (w ⬝ᵥ g j) := by
      simp only [Finset.sum_const_zero]
      linarith
    obtain ⟨j, _, hj⟩ := Finset.exists_lt_of_sum_lt hsumpos
    have hwg : 0 < w ⬝ᵥ g j := by
      by_contra h
      push Not at h
      have := mul_nonpos_iff.mpr (Or.inl ⟨hf0 j, h⟩)
      linarith
    have hfj : 1 ≤ f j := by
      have h1 : 0 < f j := by
        by_contra h
        push Not at h
        have : f j = 0 := le_antisymm h (hf0 j)
        rw [this, zero_mul] at hj
        exact lt_irrefl _ hj
      simp only [f] at h1 ⊢
      have : (0 : ℤ) < ⌊c j⌋ := by exact_mod_cast h1
      exact_mod_cast this
    have hcj : 1 ≤ c j := hfj.trans (hfle j)
    have hzg : z + g j ∈ polyhedron A b := by
      show Am *ᵥ (z + g j) ≤ b
      intro i
      rw [mulVec_add, Pi.add_apply]
      by_cases hi : 0 ≤ (Am *ᵥ d) i
      · have h1 : (Am *ᵥ g j) i ≤ c j * (Am *ᵥ g j) i := by
          nlinarith [hpos i hi j]
        have h2 : c j * (Am *ᵥ g j) i ≤ ∑ l, c l * (Am *ᵥ g l) i :=
          Finset.single_le_sum (f := fun l => c l * (Am *ᵥ g l) i)
            (fun l _ => mul_nonneg (hc l) (hpos i hi l)) (Finset.mem_univ j)
        have h3 := hAd i
        rw [hAd'] at h3
        have h4 : (Am *ᵥ y) i ≤ b i := hyP i
        linarith
      · push Not at hi
        have h1 := hneg i hi j
        have h2 : (Am *ᵥ z) i ≤ b i := hzP i
        linarith
    refine ⟨z + g j, isIntegral_add hz (hgI j), hzg, ?_, ?_⟩
    · have : z - (z + g j) = -(g j) := by abel
      rw [this, supNorm_neg]
      have hn1 : (1 : ℚ) ≤ n := by
        have : 1 ≤ k := by have := j.isLt; omega
        have : 1 ≤ n := by omega
        exact_mod_cast this
      calc supNorm (g j) ≤ (maxSubdet A : ℚ) := hgN j
        _ = 1 * (maxSubdet A : ℚ) := by ring
        _ ≤ (n : ℚ) * (maxSubdet A : ℚ) := mul_le_mul_of_nonneg_right hn1 (Nat.cast_nonneg _)
    · rw [dotProduct_add]
      linarith

/-! ### Section 4: Fourier–Motzkin and Farkas' Lemma over `ℚ` -/

lemma fm_between_rat {ι : Type*} [Fintype ι] (α l u : ι → ℚ)
    (h : ∀ p q, 0 < α p → α q < 0 → l q ≤ u p) :
    ∃ t : ℚ, (∀ q, α q < 0 → l q ≤ t) ∧ ∀ p, 0 < α p → t ≤ u p := by
  by_cases hN : (Finset.univ.filter (fun q => α q < 0)).Nonempty
  · obtain ⟨q0, hq0, hmax⟩ := Finset.exists_max_image _ l hN
    refine ⟨l q0, fun q hq => hmax q (by simpa using hq),
      fun p hp => h p q0 hp (by simpa using hq0)⟩
  · by_cases hP : (Finset.univ.filter (fun p => 0 < α p)).Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := Finset.exists_min_image _ u hP
      refine ⟨u p0, fun q hq => ?_, fun p hp => hmin p (by simpa using hp)⟩
      exact absurd ⟨q, by simpa using hq⟩ hN
    · refine ⟨0, fun q hq => ?_, fun p hp => ?_⟩
      · exact absurd ⟨q, by simpa using hq⟩ hN
      · exact absurd ⟨p, by simpa using hp⟩ hP

theorem farkas_rat : ∀ (n : ℕ) {ι : Type*} [Fintype ι] (a : ι → Fin n → ℚ) (b : ι → ℚ),
    (¬ ∃ x : Fin n → ℚ, ∀ i, a i ⬝ᵥ x ≤ b i) →
    ∃ μ : ι → ℚ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • a i = 0) ∧ ∑ i, μ i * b i < 0 := by
  intro n
  induction n with
  | zero =>
    intro ι _ a b h
    have : ∃ i, b i < 0 := by
      by_contra hc
      push Not at hc
      exact h ⟨0, fun i => by simpa using hc i⟩
    obtain ⟨i0, hi0⟩ := this
    refine ⟨fun i => if i = i0 then 1 else 0,
      fun i => by dsimp only; split_ifs <;> norm_num, ?_, ?_⟩
    · funext j; exact j.elim0
    · simpa using hi0
  | succ n ih =>
    intro ι _ a b h
    set α : ι → ℚ := fun i => a i 0 with hα
    set a' : ι → Fin n → ℚ := fun i j => a i j.succ with ha'
    have hdot : ∀ i (t : ℚ) (x' : Fin n → ℚ),
        a i ⬝ᵥ (vecCons t x') = α i * t + a' i ⬝ᵥ x' := by
      intro i t x'
      simp only [dotProduct, Fin.sum_univ_succ, hα, ha']
      simp
    let W : ι × ι → ι → ℚ := fun pq l =>
      (if α pq.1 = 0 ∧ pq.1 = pq.2 ∧ l = pq.1 then 1 else 0) +
      (if 0 < α pq.1 ∧ α pq.2 < 0 then
        ((if l = pq.1 then -α pq.2 else 0) + (if l = pq.2 then α pq.1 else 0)) else 0)
    have hW0 : ∀ pq l, 0 ≤ W pq l := by
      intro pq l
      simp only [W]
      split_ifs <;> linarith
    have hW1 : ∀ i, α i = 0 → ∀ v : ι → ℚ, ∑ l, W (i, i) l * v l = v i := by
      intro i hi v
      have : ∀ l, W (i, i) l = if l = i then 1 else 0 := by
        intro l; simp [W, hi]
      simp [this]
    have hW2 : ∀ p q, 0 < α p → α q < 0 → ∀ v : ι → ℚ,
        ∑ l, W (p, q) l * v l = -α q * v p + α p * v q := by
      intro p q hp hq v
      have hpq : p ≠ q := fun e => by subst e; linarith
      have : ∀ l, W (p, q) l = (if l = p then -α q else 0) + (if l = q then α p else 0) := by
        intro l; simp [W, hp, hq, hp.ne', hpq]
      simp [this, add_mul, Finset.sum_add_distrib]
    have hW3 : ∀ p q, ¬ (α p = 0 ∧ p = q) → ¬ (0 < α p ∧ α q < 0) → ∀ v : ι → ℚ,
        ∑ l, W (p, q) l * v l = 0 := by
      intro p q h1 h2 v
      have : ∀ l, W (p, q) l = 0 := by
        intro l
        have h1' : ¬ (α p = 0 ∧ p = q ∧ l = p) := fun h => h1 ⟨h.1, h.2.1⟩
        simp only [W]; rw [if_neg h1', if_neg h2]; simp
      simp [this]
    have hWα : ∀ pq, ∑ l, W pq l * α l = 0 := by
      intro pq
      obtain ⟨p, q⟩ := pq
      by_cases h1 : α p = 0 ∧ p = q
      · obtain ⟨h1a, rfl⟩ := h1
        rw [hW1 p h1a]; exact h1a
      · by_cases h2 : 0 < α p ∧ α q < 0
        · rw [hW2 p q h2.1 h2.2]; ring
        · exact hW3 p q h1 h2 _
    let a'' : ι × ι → Fin n → ℚ := fun pq => ∑ l, W pq l • a' l
    let b'' : ι × ι → ℚ := fun pq => ∑ l, W pq l * b l
    have hinf : ¬ ∃ x' : Fin n → ℚ, ∀ pq, a'' pq ⬝ᵥ x' ≤ b'' pq := by
      rintro ⟨x', hx'⟩
      have hex := fm_between_rat α (fun q => (b q - a' q ⬝ᵥ x') / α q)
        (fun p => (b p - a' p ⬝ᵥ x') / α p) (by
          intro p q hp hq
          have := hx' (p, q)
          have e1 : a'' (p, q) ⬝ᵥ x' = ∑ l, W (p, q) l * (a' l ⬝ᵥ x') := by
            simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          rw [e1] at this
          have hsum : ∑ l, W (p, q) l * (a' l ⬝ᵥ x') = -α q * (a' p ⬝ᵥ x') + α p * (a' q ⬝ᵥ x') :=
            hW2 p q hp hq _
          have hb : b'' (p, q) = -α q * b p + α p * b q := hW2 p q hp hq _
          rw [hsum, hb] at this
          rw [div_le_iff_of_neg hq, div_mul_eq_mul_div, div_le_iff₀ hp]
          nlinarith)
      obtain ⟨t, htl, htu⟩ := hex
      apply h
      refine ⟨vecCons t x', fun i => ?_⟩
      rw [hdot]
      rcases lt_trichotomy (α i) 0 with hi | hi | hi
      · have := htl i hi
        rw [div_le_iff_of_neg hi] at this
        linarith
      · have := hx' (i, i)
        have e1 : a'' (i, i) ⬝ᵥ x' = a' i ⬝ᵥ x' := by
          simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          exact hW1 i hi (fun l => a' l ⬝ᵥ x')
        have e2 : b'' (i, i) = b i := hW1 i hi b
        rw [e1, e2] at this
        rw [hi]; linarith
      · have := htu i hi
        rw [le_div_iff₀ hi] at this
        linarith
    obtain ⟨μ'', hμ0, hμa, hμb⟩ := ih a'' b'' hinf
    refine ⟨fun l => ∑ pq, μ'' pq * W pq l,
      fun l => Finset.sum_nonneg (fun pq _ => mul_nonneg (hμ0 pq) (hW0 pq l)), ?_, ?_⟩
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have : ∀ l, a l 0 = α l := fun l => rfl
        simp only [this]
        calc ∑ l, (∑ pq, μ'' pq * W pq l) * α l
            = ∑ pq, μ'' pq * ∑ l, W pq l * α l := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by simp [hWα]
      · have := congrFun hμa j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, a''] at this ⊢
        have e : ∀ l, a l j.succ = a' l j := fun l => rfl
        simp only [e]
        calc ∑ l, (∑ pq, μ'' pq * W pq l) * a' l j
            = ∑ pq, μ'' pq * ∑ l, W pq l * a' l j := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by rw [← this]
    · calc ∑ l, (∑ pq, μ'' pq * W pq l) * b l
          = ∑ pq, μ'' pq * b'' pq := by
            simp only [b'', Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ < 0 := hμb

theorem farkas_fintype_rat {α ι : Type*} [Fintype α] [Fintype ι]
    (a : ι → α → ℚ) (b : ι → ℚ)
    (h : ¬ ∃ x : α → ℚ, ∀ i, (∑ v : α, a i v * x v) ≤ b i) :
    ∃ μ : ι → ℚ, (∀ i, 0 ≤ μ i) ∧ (∀ v : α, ∑ i, μ i * a i v = 0) ∧ ∑ i, μ i * b i < 0 := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let a' : ι → Fin (Fintype.card α) → ℚ := fun i j => a i (e.symm j)
  have h' : ¬ ∃ x : Fin (Fintype.card α) → ℚ, ∀ i, a' i ⬝ᵥ x ≤ b i := by
    rintro ⟨x, hx⟩
    apply h
    refine ⟨fun v => x (e v), fun i => ?_⟩
    have := hx i
    have hsum : (∑ v : α, a i v * x (e v)) = a' i ⬝ᵥ x := by
      simp only [dotProduct, a']
      simpa using e.sum_comp (fun j => a i (e.symm j) * x j)
    linarith
  obtain ⟨μ, hμ0, hμa, hμb⟩ := farkas_rat (Fintype.card α) a' b h'
  refine ⟨μ, hμ0, fun v => ?_, hμb⟩
  have hv := congrFun hμa (e v)
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, a'] using hv

/-! ### Section 5: Determinant bound, recession generators, and `integerHull_eq_of_bounded_matrix` -/

lemma det_natAbs_le_of_abs_le {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ) (K : ℕ)
    (hS : ∀ i j, |S i j| ≤ (K : ℤ)) :
    S.det.natAbs ≤ r ^ r * K ^ r := by
  have h_abs : |S.det| ≤ ((r ^ r * K ^ r : ℕ) : ℤ) := by
    rw [Matrix.det_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h_term : ∀ σ : Equiv.Perm (Fin r),
        |Equiv.Perm.sign σ • ∏ i : Fin r, S (σ i) i| ≤ ((K ^ r : ℕ) : ℤ) := by
      intro σ
      have h_prod : (∏ i : Fin r, |S (σ i) i|) ≤ ∏ _i : Fin r, (K : ℤ) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hS (σ i) i)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul, Finset.abs_prod]
        simpa using h_prod
      · rw [h, Units.neg_smul, one_smul, abs_neg, Finset.abs_prod]
        simpa using h_prod
    have h_sum : (∑ σ : Equiv.Perm (Fin r), |Equiv.Perm.sign σ • ∏ i : Fin r, S (σ i) i|) ≤
        ∑ _σ : Equiv.Perm (Fin r), ((K ^ r : ℕ) : ℤ) :=
      Finset.sum_le_sum fun σ _ => h_term σ
    refine h_sum.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
    exact_mod_cast Nat.mul_le_mul_right (K ^ r) (Nat.factorial_le_pow r)
  have h2 : (S.det.natAbs : ℤ) ≤ ((r ^ r * K ^ r : ℕ) : ℤ) := by
    rwa [Int.natCast_natAbs]
  exact_mod_cast h2

lemma maxSubdet_le_of_entry_bound {m' n : ℕ} (B : Matrix (Fin m') (Fin n) ℤ) (Δ : ℕ)
    (hB : ∀ i j, |B i j| ≤ ((n * Δ : ℕ) : ℤ)) :
    maxSubdet B ≤ n ^ (2 * n) * Δ ^ n := by
  unfold maxSubdet
  refine Finset.sup_le fun k _ => Finset.sup_le fun f _ => Finset.sup_le fun g _ => ?_
  let r := k.val + 1
  have hr_le_n : r ≤ n := by have := k.isLt; omega
  have hr_pos : 1 ≤ r := by omega
  have hn_pos : 1 ≤ n := by omega
  have h1 : (B.submatrix f g).det.natAbs ≤ r ^ r * (n * Δ) ^ r :=
    det_natAbs_le_of_abs_le (B.submatrix f g) (n * Δ) (fun i j => hB (f i) (g j))
  have h2 : r ^ r ≤ n ^ n :=
    (Nat.pow_le_pow_left hr_le_n r).trans (Nat.pow_le_pow_right hn_pos hr_le_n)
  have h3 : (n * Δ) ^ r ≤ (n * Δ) ^ n := by
    rcases Nat.eq_zero_or_pos (n * Δ) with h0 | hpos
    · rw [h0, zero_pow (by omega), zero_pow (by omega)]
    · exact Nat.pow_le_pow_right hpos hr_le_n
  calc (B.submatrix f g).det.natAbs
      ≤ r ^ r * (n * Δ) ^ r := h1
    _ ≤ n ^ n * (n * Δ) ^ n := Nat.mul_le_mul h2 h3
    _ = n ^ (2 * n) * Δ ^ n := by
        rw [Nat.mul_pow, ← mul_assoc, ← pow_add, ← two_mul]

lemma integerHull_univ_eq {n : ℕ} (hn : 1 ≤ n) :
    convexHull ℚ {z : Fin n → ℚ | IsIntegral z} = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  have h_single_int : ∀ (j : Fin n) (k : ℤ),
      Pi.single j (k : ℚ) ∈ convexHull ℚ {z : Fin n → ℚ | IsIntegral z} := by
    intro j k
    refine subset_convexHull ℚ {z : Fin n → ℚ | IsIntegral z} ?_
    intro i
    by_cases hij : i = j
    · subst hij; exact ⟨k, by simp⟩
    · exact ⟨0, by simp [hij]⟩
  have h_single_rat : ∀ (j : Fin n) (q : ℚ),
      Pi.single j q ∈ convexHull ℚ {z : Fin n → ℚ | IsIntegral z} := by
    intro j q
    let k : ℤ := ⌊q⌋
    let t : ℚ := q - k
    have ht0 : 0 ≤ t := sub_nonneg.mpr (Int.floor_le q)
    have ht1 : 0 ≤ 1 - t := by
      have := Int.lt_floor_add_one q
      dsimp only [t, k]
      linarith
    have h_comb : (1 - t) • Pi.single j (k : ℚ) + t • Pi.single j ((k + 1 : ℤ) : ℚ) =
        Pi.single j q := by
      ext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Int.cast_add,
          Int.cast_one, t]
        ring
      · simp [hij]
    rw [← h_comb]
    exact (convex_convexHull ℚ _) (h_single_int j k) (h_single_int j (k + 1)) ht1 ht0 (by ring)
  have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn
  have h_sum_x : (∑ j : Fin n, (n : ℚ)⁻¹ • Pi.single j ((n : ℚ) * x j)) = x := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← mul_assoc, inv_mul_cancel₀ hn_pos.ne',
      one_mul]
  rw [← h_sum_x]
  refine (convex_convexHull ℚ _).sum_mem (fun j _ => inv_nonneg.mpr hn_pos.le) ?_
    (fun j _ => h_single_rat j ((n : ℚ) * x j))
  simp [mul_inv_cancel₀ hn_pos.ne']

lemma finite_integral_of_supNorm_le {n : ℕ} (S : Set (Fin n → ℚ)) (K : ℚ)
    (hI : ∀ x ∈ S, IsIntegral x) (hB : ∀ x ∈ S, supNorm x ≤ K) : S.Finite := by
  let B : ℤ := ⌈max 0 K⌉
  have hfin : (Set.Icc (fun _ : Fin n => -B) (fun _ => B)).Finite := Set.finite_Icc _ _
  refine (hfin.image (fun (v : Fin n → ℤ) (j : Fin n) => (v j : ℚ))).subset ?_
  intro x hx
  choose v hv using hI x hx
  refine ⟨v, ⟨fun j => ?_, fun j => ?_⟩, funext fun j => (hv j).symm⟩
  · have h1 : |x j| ≤ max 0 K := (abs_le_supNorm x j).trans ((hB x hx).trans (le_max_right 0 K))
    have h2 : |(v j : ℚ)| ≤ (B : ℚ) := by rw [← hv j]; exact h1.trans (Int.le_ceil _)
    have h3 : |v j| ≤ B := by exact_mod_cast h2
    exact (abs_le.mp h3).1
  · have h1 : |x j| ≤ max 0 K := (abs_le_supNorm x j).trans ((hB x hx).trans (le_max_right 0 K))
    have h2 : |(v j : ℚ)| ≤ (B : ℚ) := by rw [← hv j]; exact h1.trans (Int.le_ceil _)
    have h3 : |v j| ≤ B := by exact_mod_cast h2
    exact (abs_le.mp h3).2

def G_rec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Set (Fin n → ℚ) :=
  {g | IsIntegral g ∧ (A.map (Int.cast : ℤ → ℚ)) *ᵥ g ≤ 0 ∧ supNorm g ≤ (maxSubdet A : ℚ)}

lemma G_rec_finite {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : (G_rec A).Finite :=
  finite_integral_of_supNorm_le (G_rec A) (maxSubdet A : ℚ) (fun _ hg => hg.1) (fun _ hg => hg.2.2)

lemma add_coneSpan_G_rec_mem_integerHull {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) {y v : Fin n → ℚ} (hy : y ∈ integerHull (polyhedron A b))
    (hv : v ∈ coneSpan (G_rec A)) : y + v ∈ integerHull (polyhedron A b) := by
  have h_step : ∀ (g : Fin n → ℚ), g ∈ G_rec A → ∀ (c : ℚ), 0 ≤ c →
      ∀ x ∈ integerHull (polyhedron A b), x + c • g ∈ integerHull (polyhedron A b) := by
    intro g hg c hc x hx
    have h_nat : ∀ (N_nat : ℕ) (x' : Fin n → ℚ), x' ∈ integerHull (polyhedron A b) →
        x' + (N_nat : ℚ) • g ∈ integerHull (polyhedron A b) := by
      intro N_nat
      let T : Set (Fin n → ℚ) := {x' | x' + (N_nat : ℚ) • g ∈ integerHull (polyhedron A b)}
      have hT_conv : Convex ℚ T := by
        intro u hu w hw a1 b1 ha1 hb1 hab1
        show (a1 • u + b1 • w) + (N_nat : ℚ) • g ∈ integerHull (polyhedron A b)
        have h_eq : (a1 • u + b1 • w) + (N_nat : ℚ) • g =
            a1 • (u + (N_nat : ℚ) • g) + b1 • (w + (N_nat : ℚ) • g) := by
          ext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          calc a1 * u j + b1 * w j + (N_nat : ℚ) * g j
              = a1 * u j + b1 * w j + (a1 + b1) * ((N_nat : ℚ) * g j) := by rw [hab1, one_mul]
            _ = a1 * (u j + (N_nat : ℚ) * g j) + b1 * (w j + (N_nat : ℚ) * g j) := by ring
        rw [h_eq]
        exact (convex_convexHull ℚ _) hu hw ha1 hb1 hab1
      have hT_sub : {z | z ∈ polyhedron A b ∧ IsIntegral z} ⊆ T := by
        rintro z ⟨hzP, hzI⟩
        refine subset_convexHull ℚ {z | z ∈ polyhedron A b ∧ IsIntegral z} ⟨?_, ?_⟩
        · intro i
          rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h1 := hzP i
          have h2 := hg.2.1 i
          have h3 : (N_nat : ℚ) * ((A.map (Int.cast : ℤ → ℚ) *ᵥ g) i) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N_nat) h2
          linarith
        · exact isIntegral_add hzI (isIntegral_intSmul (N_nat : ℤ) hg.1)
      exact convexHull_min hT_sub hT_conv
    let M_nat : ℕ := ⌈c⌉₊ + 1
    have hM_pos : (0 : ℚ) < M_nat := by positivity
    have hc_le : c ≤ M_nat := by
      have : c ≤ (⌈c⌉₊ : ℚ) := Nat.le_ceil c
      dsimp only [M_nat]
      push_cast
      linarith
    have ht0 : 0 ≤ c / M_nat := div_nonneg hc hM_pos.le
    have ht1 : 0 ≤ 1 - c / M_nat := by
      rw [sub_nonneg, div_le_one hM_pos]
      exact hc_le
    have h_comb : x + c • g = (1 - c / M_nat) • x + (c / M_nat) • (x + (M_nat : ℚ) • g) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [h_comb]
    exact (convex_convexHull ℚ _) hx (h_nat M_nat x hx) ht1 ht0 (by ring)
  obtain ⟨k, g, c, hg, hc, rfl⟩ := hv
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    have hy' := ih (fun j => g (Fin.castSucc j)) (fun j => c (Fin.castSucc j))
      (fun j => hg _) (fun j => hc _)
    exact h_step (g (Fin.last k)) (hg (Fin.last k)) (c (Fin.last k)) (hc (Fin.last k)) _ hy'

lemma S_b_decomp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0) (b : Fin m → ℚ)
    (x₀ : Fin n → ℚ) (hx₀P : x₀ ∈ polyhedron A b) (hx₀I : IsIntegral x₀) :
    let M_b : ℚ := Finset.univ.fold max 0
      (fun i : Fin m => b i - ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x₀) i)
    let R_b : ℚ := (n : ℚ) * (M_b + 1) * (maxSubdet A : ℚ)
    ∀ z ∈ polyhedron A b, IsIntegral z →
      ∃ z', z' ∈ polyhedron A b ∧ IsIntegral z' ∧ supNorm (z' - x₀) ≤ R_b ∧
        z - z' ∈ coneSpan (G_rec A) := by
  intro M_b R_b z hzP hzI
  set Am := A.map (Int.cast : ℤ → ℚ) with hAm
  have hMb_nonneg : 0 ≤ M_b := by
    dsimp only [M_b]
    rw [Finset.le_fold_max]
    exact Or.inl le_rfl
  have hMb_ge : ∀ i : Fin m, b i - (Am *ᵥ x₀) i ≤ M_b := by
    intro i
    dsimp only [M_b]
    rw [Finset.le_fold_max]
    exact Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩
  set d := z - x₀ with hd
  let s : Fin m → ℚ := fun i => if 0 ≤ (Am *ᵥ d) i then -1 else 1
  have hs : ∀ i, s i ≠ 0 := by intro i; simp only [s]; split_ifs <;> norm_num
  have hdC : ∀ i, s i * (Am *ᵥ d) i ≤ 0 := by
    intro i; simp only [s]; split_ifs with h <;> linarith
  obtain ⟨k, g, c, hk, hgI, hgC, hgN, hc, hsum⟩ := decomposition A hA s hs d hdC
  have hpos : ∀ i, 0 ≤ (Am *ᵥ d) i → ∀ j, 0 ≤ (Am *ᵥ g j) i := by
    intro i hi j; have := hgC j i; simp only [s, if_pos hi] at this; linarith
  have hneg : ∀ i, (Am *ᵥ d) i < 0 → ∀ j, (Am *ᵥ g j) i ≤ 0 := by
    intro i hi j; have := hgC j i; simp only [s, if_neg (not_le.mpr hi)] at this; linarith
  have hAd : ∀ i, (Am *ᵥ d) i = ∑ j, c j * (Am *ᵥ g j) i := fun i => by
    rw [hsum]; exact mulVec_sum_smul Am c g i
  have hAd' : ∀ i, (Am *ᵥ d) i = (Am *ᵥ z) i - (Am *ᵥ x₀) i := fun i => by
    rw [hd, mulVec_sub]; rfl
  let f : Fin k → ℚ := fun j => if Am *ᵥ g j ≤ 0 then (⌊c j⌋ : ℚ) else 0
  have hf0 : ∀ j, 0 ≤ f j := by
    intro j; dsimp only [f]; split_ifs
    · exact_mod_cast Int.floor_nonneg.mpr (hc j)
    · exact le_rfl
  have hfle : ∀ j, f j ≤ c j := by
    intro j; dsimp only [f]; split_ifs
    · exact Int.floor_le (c j)
    · exact hc j
  have hdiff_le : ∀ j, c j - f j ≤ M_b + 1 := by
    intro j; dsimp only [f]
    split_ifs with hrec
    · have := Int.lt_floor_add_one (c j)
      linarith
    · rw [Pi.le_def] at hrec
      push Not at hrec
      obtain ⟨i₀, hi₀⟩ := hrec
      simp only [Pi.zero_apply] at hi₀
      have hd_i₀ : 0 ≤ (Am *ᵥ d) i₀ := by
        by_contra hlt
        push Not at hlt
        have := hneg i₀ hlt j
        linarith
      obtain ⟨zz, hzz⟩ := mulVec_integral A (hgI j) i₀
      have h_ge_one : 1 ≤ (Am *ᵥ g j) i₀ := by
        rw [hzz] at hi₀ ⊢
        have : 0 < zz := by exact_mod_cast hi₀
        have : 1 ≤ zz := by omega
        exact_mod_cast this
      have h_single : c j * (Am *ᵥ g j) i₀ ≤ ∑ l, c l * (Am *ᵥ g l) i₀ :=
        Finset.single_le_sum (f := fun l => c l * (Am *ᵥ g l) i₀)
          (fun l _ => mul_nonneg (hc l) (hpos i₀ hd_i₀ l)) (Finset.mem_univ j)
      have h1 : c j ≤ c j * (Am *ᵥ g j) i₀ := by nlinarith [hc j]
      have h2 := hAd i₀
      rw [hAd'] at h2
      have h3 : (Am *ᵥ z) i₀ ≤ b i₀ := hzP i₀
      have h4 := hMb_ge i₀
      linarith
  set v := ∑ j, f j • g j with hv
  have hv_cone : v ∈ coneSpan (G_rec A) := by
    refine coneSpan_sum k (fun j => f j • g j) (fun j => ?_)
    dsimp only [f]
    split_ifs with hrec
    · exact smul_mem_coneSpan (G := G_rec A) ⟨hgI j, hrec, hgN j⟩
        (by exact_mod_cast Int.floor_nonneg.mpr (hc j))
    · simp [zero_mem_coneSpan]
  have hvI : IsIntegral v := by
    refine isIntegral_sum _ _ (fun j _ => ?_)
    dsimp only [f]
    split_ifs
    · exact isIntegral_intSmul _ (hgI j)
    · simpa using isIntegral_zero
  set z' := z - v with hz'
  have hz'I : IsIntegral z' := isIntegral_sub hzI hvI
  have hAv : ∀ i, (Am *ᵥ v) i = ∑ j, f j * (Am *ᵥ g j) i := fun i => mulVec_sum_smul Am f g i
  have hz'P : z' ∈ polyhedron A b := by
    show Am *ᵥ z' ≤ b
    intro i
    rw [hz', mulVec_sub, Pi.sub_apply, hAv]
    by_cases hi : 0 ≤ (Am *ᵥ d) i
    · have h1 : 0 ≤ ∑ j, f j * (Am *ᵥ g j) i :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hf0 j) (hpos i hi j)
      have h2 : (Am *ᵥ z) i ≤ b i := hzP i
      linarith
    · push Not at hi
      have h1 : ∑ j, (c j - f j) * (Am *ᵥ g j) i ≤ 0 :=
        Finset.sum_nonpos fun j _ =>
          mul_nonpos_iff.mpr (Or.inl ⟨by linarith [hfle j], hneg i hi j⟩)
      have h2 : (Am *ᵥ x₀) i ≤ b i := hx₀P i
      have h3 := hAd i
      rw [hAd'] at h3
      simp only [sub_mul, Finset.sum_sub_distrib] at h1
      linarith
  have hz'x₀ : z' - x₀ = ∑ j, (c j - f j) • g j := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← hsum, ← hv, hz', hd]
    abel
  have hz'B : supNorm (z' - x₀) ≤ R_b := by
    rw [hz'x₀]
    refine (supNorm_sum_smul_le _ _ _ (fun j => by linarith [hfle j]) hgN).trans ?_
    have h_sum_le : ∑ j, (c j - f j) ≤ (k : ℚ) * (M_b + 1) := by
      calc ∑ j, (c j - f j) ≤ ∑ _j : Fin k, (M_b + 1) := Finset.sum_le_sum fun j _ => hdiff_le j
        _ = (k : ℚ) * (M_b + 1) := by simp; ring
    have hk' : (k : ℚ) ≤ n := by exact_mod_cast hk
    have h_kn : (k : ℚ) * (M_b + 1) ≤ (n : ℚ) * (M_b + 1) :=
      mul_le_mul_of_nonneg_right hk' (by linarith)
    exact mul_le_mul_of_nonneg_right (h_sum_le.trans h_kn) (Nat.cast_nonneg _)
  refine ⟨z', hz'P, hz'I, hz'B, ?_⟩
  have : z - z' = v := by dsimp only [z']; abel
  rw [this]
  exact hv_cone

theorem integerHull_eq_of_bounded_matrix_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin n) ℤ),
      (∀ i j, |M i j| ≤ ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℤ)) ∧
      ∀ b : Fin m → ℚ, (∃ x ∈ polyhedron A b, IsIntegral x) →
        ∃ d : Fin N → ℚ,
          integerHull (polyhedron A b) = {x | (M.map (Int.cast : ℤ → ℚ)) *ᵥ x ≤ d} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · refine ⟨0, Matrix.of (fun i : Fin 0 => i.elim0), fun i => i.elim0, fun b ⟨x₀, hx₀P, hx₀I⟩ => ?_⟩
    refine ⟨fun i : Fin 0 => i.elim0, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro _ i; exact i.elim0
    · intro _
      have hx : x = x₀ := Subsingleton.elim x x₀
      rw [hx]
      exact subset_convexHull ℚ {z | z ∈ polyhedron A b ∧ IsIntegral z} ⟨hx₀P, hx₀I⟩
  by_cases hA : A = 0
  · subst hA
    refine ⟨0, Matrix.of (fun i : Fin 0 => i.elim0), fun i => i.elim0, fun b ⟨x₀, hx₀P, _⟩ => ?_⟩
    refine ⟨fun i : Fin 0 => i.elim0, ?_⟩
    have huniv := polyhedron_zero b x₀ hx₀P
    have h_ih : integerHull (polyhedron (0 : Matrix (Fin m) (Fin n) ℤ) b) = Set.univ := by
      unfold integerHull
      simp only [huniv, Set.mem_univ, true_and]
      exact integerHull_univ_eq hn_pos
    rw [h_ih]
    ext x
    simp only [Set.mem_univ, Set.mem_ofPred_eq, true_iff]
    intro i; exact i.elim0
  -- Main case: `1 ≤ n` and `A ≠ 0`
  let B_bound : ℤ := ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℤ)
  have hΔ_pos : 1 ≤ maxSubdet A := by
    obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
      by_contra h; push Not at h; exact hA (Matrix.ext h)
    have h1 := natAbs_det_submatrix_le A hA 1 (fun _ => i) (fun _ => j)
      (fun a b _ => Subsingleton.elim a b) (fun a b _ => Subsingleton.elim a b)
    change (A.submatrix (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)).det.natAbs ≤ _ at h1
    rw [Matrix.det_fin_one] at h1
    simp only [Matrix.submatrix_apply] at h1
    have h2 : 0 < (A i j).natAbs := Int.natAbs_pos.mpr hij
    omega
  have hB_bound_pos : 1 ≤ B_bound := by
    have : 1 ≤ n ^ (2 * n) * maxSubdet A ^ n :=
      Nat.mul_pos (Nat.pow_pos hn_pos) (Nat.pow_pos hΔ_pos)
    dsimp only [B_bound]
    exact_mod_cast this
  let RowsSet : Set (Fin n → ℤ) :=
    {w | (∀ j, |w j| ≤ B_bound) ∧ (∀ g ∈ G_rec A, (fun j => (w j : ℚ)) ⬝ᵥ g ≤ 0)}
  have hRows_fin : RowsSet.Finite := by
    refine (Set.finite_Icc (fun _ : Fin n => -B_bound) (fun _ => B_bound)).subset ?_
    intro w hw
    exact ⟨fun j => (abs_le.mp (hw.1 j)).1, fun j => (abs_le.mp (hw.1 j)).2⟩
  have : Fintype RowsSet := hRows_fin.fintype
  let N := Fintype.card RowsSet
  let eqv : Fin N ≃ RowsSet := (Fintype.equivFin RowsSet).symm
  let M : Matrix (Fin N) (Fin n) ℤ := Matrix.of fun i j => (eqv i).1 j
  refine ⟨N, M, fun i j => (eqv i).2.1 j, fun b ⟨x₀, hx₀P, hx₀I⟩ => ?_⟩
  let M_b : ℚ := Finset.univ.fold max 0
    (fun i : Fin m => b i - ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x₀) i)
  let R_b : ℚ := (n : ℚ) * (M_b + 1) * (maxSubdet A : ℚ)
  have h_decomp := S_b_decomp A hA b x₀ hx₀P hx₀I
  -- Every `w` satisfying `∀ g ∈ G_rec A, w ⬝ᵥ g ≤ 0` is bounded on `S_b`
  have h_w_bdd : ∀ w : Fin n → ℚ, (∀ g ∈ G_rec A, w ⬝ᵥ g ≤ 0) →
      ∃ B_w : ℚ, ∀ z ∈ polyhedron A b, IsIntegral z → w ⬝ᵥ z ≤ B_w := by
    intro w hw
    refine ⟨w ⬝ᵥ x₀ + l1Norm w * max 0 R_b, fun z hzP hzI => ?_⟩
    obtain ⟨z', _, _, hz'B, hzz'_cone⟩ := h_decomp z hzP hzI
    obtain ⟨k, g, c, hg, hc, hzz'_eq⟩ := hzz'_cone
    have hw_cone : w ⬝ᵥ (z - z') ≤ 0 := by
      rw [hzz'_eq, dot_sum_smul]
      exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hc j) (hw (g j) (hg j))
    have hw_z' : w ⬝ᵥ (z' - x₀) ≤ l1Norm w * max 0 R_b := by
      calc w ⬝ᵥ (z' - x₀)
          ≤ ∑ j : Fin n, |w j| * supNorm (z' - x₀) := by
            unfold dotProduct
            refine Finset.sum_le_sum fun j _ => ?_
            refine (le_abs_self _).trans ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (abs_le_supNorm (z' - x₀) j) (abs_nonneg _)
        _ = l1Norm w * supNorm (z' - x₀) := by rw [l1Norm, Finset.sum_mul]
        _ ≤ l1Norm w * max 0 R_b := by
            refine mul_le_mul_of_nonneg_left (hz'B.trans (le_max_right 0 R_b)) ?_
            exact Finset.sum_nonneg fun j _ => abs_nonneg _
    have : w ⬝ᵥ z = w ⬝ᵥ x₀ + w ⬝ᵥ (z' - x₀) + w ⬝ᵥ (z - z') := by
      simp only [dotProduct_sub]; ring
    linarith
  have h_opt_i : ∀ i : Fin N, ∃ z_i, IsIPOptimal A b (fun j => (M i j : ℚ)) z_i := by
    intro i
    exact exists_ip_optimal A b (fun j => (M i j : ℚ)) ⟨x₀, hx₀P, hx₀I⟩
      (h_w_bdd (fun j => (M i j : ℚ)) (eqv i).2.2)
  choose z_opt hz_opt using h_opt_i
  let d : Fin N → ℚ := fun i => (fun j => (M i j : ℚ)) ⬝ᵥ z_opt i
  refine ⟨d, ?_⟩
  apply Set.Subset.antisymm
  · -- `integerHull (polyhedron A b) ⊆ {x | M x ≤ d}`
    have h_conv : Convex ℚ {x : Fin n → ℚ | (M.map (Int.cast : ℤ → ℚ)) *ᵥ x ≤ d} := by
      intro x hx y hy a1 b1 ha1 hb1 hab1 i
      rw [mulVec_add, mulVec_smul, mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        smul_eq_mul, smul_eq_mul]
      calc a1 * ((M.map (Int.cast : ℤ → ℚ)) *ᵥ x) i + b1 * ((M.map (Int.cast : ℤ → ℚ)) *ᵥ y) i
          ≤ a1 * d i + b1 * d i := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha1)
              (mul_le_mul_of_nonneg_left (hy i) hb1)
        _ = (a1 + b1) * d i := by ring
        _ = d i := by rw [hab1, one_mul]
    refine convexHull_min ?_ h_conv
    rintro z ⟨hzP, hzI⟩ i
    show ((M.map (Int.cast : ℤ → ℚ)) *ᵥ z) i ≤ d i
    have h_eq : ((M.map (Int.cast : ℤ → ℚ)) *ᵥ z) i = (fun j => (M i j : ℚ)) ⬝ᵥ z := by
      simp [Matrix.mulVec, dotProduct]
    rw [h_eq]
    exact (hz_opt i).2.2 z hzP hzI
  · -- `{x | M x ≤ d} ⊆ integerHull (polyhedron A b)`
    intro xstar hxstar
    by_contra hxstar_not_mem
    -- Step 1: Separate `xstar` from `F_b + coneSpan (G_rec A)` using Farkas' lemma
    let F_b : Set (Fin n → ℚ) :=
      {z' | z' ∈ polyhedron A b ∧ IsIntegral z' ∧ supNorm (z' - x₀) ≤ R_b}
    have hFb_fin : F_b.Finite := by
      refine finite_integral_of_supNorm_le F_b (supNorm x₀ + max 0 R_b) (fun _ h => h.2.1) ?_
      intro z' hz'
      have : z' = x₀ + (z' - x₀) := by abel
      rw [this]
      exact (supNorm_add_le x₀ (z' - x₀)).trans
        (add_le_add le_rfl (hz'.2.2.trans (le_max_right 0 R_b)))
    have : Fintype F_b := hFb_fin.fintype
    have : Fintype (G_rec A) := (G_rec_finite A).fintype
    let sign_val : Bool → ℚ := fun s => if s then 1 else -1
    let a_sys : (F_b ⊕ G_rec A ⊕ Bool ⊕ (Fin n × Bool)) → (F_b ⊕ G_rec A) → ℚ := fun c v =>
      match c, v with
      | Sum.inl z, Sum.inl z' => if z' = z then -1 else 0
      | Sum.inl _, Sum.inr _ => 0
      | Sum.inr (Sum.inl g), Sum.inr g' => if g' = g then -1 else 0
      | Sum.inr (Sum.inl _), Sum.inl _ => 0
      | Sum.inr (Sum.inr (Sum.inl s)), Sum.inl _ => sign_val s
      | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr _ => 0
      | Sum.inr (Sum.inr (Sum.inr (j, s))), Sum.inl z => sign_val s * z.1 j
      | Sum.inr (Sum.inr (Sum.inr (j, s))), Sum.inr g => sign_val s * g.1 j
    let b_sys : (F_b ⊕ G_rec A ⊕ Bool ⊕ (Fin n × Bool)) → ℚ := fun c =>
      match c with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl _) => 0
      | Sum.inr (Sum.inr (Sum.inl s)) => sign_val s
      | Sum.inr (Sum.inr (Sum.inr (j, s))) => sign_val s * xstar j
    have h_sys_inf : ¬ ∃ lam : F_b ⊕ G_rec A → ℚ,
        ∀ c, (∑ v : F_b ⊕ G_rec A, a_sys c v * lam v) ≤ b_sys c := by
      rintro ⟨lam, hlam⟩
      apply hxstar_not_mem
      have hlam_z : ∀ z : F_b, 0 ≤ lam (Sum.inl z) := by
        intro z
        have h := hlam (Sum.inl z)
        simp only [Fintype.sum_sum_type, a_sys, b_sys, zero_mul, Finset.sum_const_zero, add_zero,
          ite_mul, neg_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
        linarith
      have hlam_g : ∀ g : G_rec A, 0 ≤ lam (Sum.inr g) := by
        intro g
        have h := hlam (Sum.inr (Sum.inl g))
        simp only [Fintype.sum_sum_type, a_sys, b_sys, zero_mul, Finset.sum_const_zero, zero_add,
          ite_mul, neg_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
        linarith
      have hlam_sum : (∑ z : F_b, lam (Sum.inl z)) = 1 := by
        have h1 := hlam (Sum.inr (Sum.inr (Sum.inl true)))
        have h2 := hlam (Sum.inr (Sum.inr (Sum.inl false)))
        simp only [Fintype.sum_sum_type, a_sys, b_sys, sign_val, ↓reduceIte, Bool.false_eq_true,
          one_mul, neg_mul, Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, add_zero] at h1 h2
        linarith
      have hxstar_eq : (∑ z : F_b, lam (Sum.inl z) • z.1) +
          (∑ g : G_rec A, lam (Sum.inr g) • g.1) = xstar := by
        ext j
        have h1 := hlam (Sum.inr (Sum.inr (Sum.inr (j, true))))
        have h2 := hlam (Sum.inr (Sum.inr (Sum.inr (j, false))))
        simp only [Fintype.sum_sum_type, a_sys, b_sys, sign_val, ↓reduceIte, Bool.false_eq_true,
          one_mul, neg_mul, Finset.sum_neg_distrib] at h1 h2
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have heq1 : (∑ z : F_b, z.1 j * lam (Sum.inl z)) = ∑ z : F_b, lam (Sum.inl z) * z.1 j :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        have heq2 : (∑ g : G_rec A, g.1 j * lam (Sum.inr g)) =
            ∑ g : G_rec A, lam (Sum.inr g) * g.1 j :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        linarith
      have hy_mem : (∑ z : F_b, lam (Sum.inl z) • z.1) ∈ integerHull (polyhedron A b) :=
        (convex_convexHull ℚ _).sum_mem (fun z _ => hlam_z z) hlam_sum
          (fun z _ => subset_convexHull ℚ _ ⟨z.2.1, z.2.2.1⟩)
      have hv_mem : (∑ g : G_rec A, lam (Sum.inr g) • g.1) ∈ coneSpan (G_rec A) := by
        let eG : Fin (Fintype.card (G_rec A)) ≃ G_rec A := (Fintype.equivFin (G_rec A)).symm
        refine ⟨Fintype.card (G_rec A), fun j => (eG j).1, fun j => lam (Sum.inr (eG j)),
          fun j => (eG j).2, fun j => hlam_g (eG j), ?_⟩
        exact (Equiv.sum_comp eG (fun g : G_rec A => lam (Sum.inr g) • g.1)).symm
      rw [← hxstar_eq]
      exact add_coneSpan_G_rec_mem_integerHull A b hy_mem hv_mem
    obtain ⟨μ, hμ0, hμa, hμb⟩ := farkas_fintype_rat a_sys b_sys h_sys_inf
    let γ : ℚ := μ (Sum.inr (Sum.inr (Sum.inl true))) - μ (Sum.inr (Sum.inr (Sum.inl false)))
    let w : Fin n → ℚ := fun j =>
      μ (Sum.inr (Sum.inr (Sum.inr (j, false)))) - μ (Sum.inr (Sum.inr (Sum.inr (j, true))))
    have hw_Fb : ∀ z : F_b, w ⬝ᵥ z.1 ≤ γ := by
      intro z
      have hz := hμa (Sum.inl z)
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, a_sys, sign_val,
        ↓reduceIte, Bool.false_eq_true, mul_zero, Finset.sum_const_zero, zero_add] at hz
      have h_s1 : (∑ z' : F_b, μ (Sum.inl z') * (if z = z' then -1 else 0)) =
          -μ (Sum.inl z) := by
        simp [mul_ite]
      have h_s4 : (∑ j : Fin n,
          (μ (Sum.inr (Sum.inr (Sum.inr (j, true)))) * (1 * z.1 j) +
           μ (Sum.inr (Sum.inr (Sum.inr (j, false)))) * (-1 * z.1 j))) = -(w ⬝ᵥ z.1) := by
        simp only [dotProduct, w, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h_s1, h_s4] at hz
      have h_nonneg := hμ0 (Sum.inl z)
      dsimp only [γ]
      linarith
    have hw_Grec : ∀ g ∈ G_rec A, w ⬝ᵥ g ≤ 0 := by
      intro g hg
      have hg_eq := hμa (Sum.inr ⟨g, hg⟩)
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, a_sys, sign_val,
        ↓reduceIte, Bool.false_eq_true, mul_zero, Finset.sum_const_zero, zero_add] at hg_eq
      have h_s2 : (∑ g' : G_rec A, μ (Sum.inr (Sum.inl g')) *
          (if (⟨g, hg⟩ : G_rec A) = g' then -1 else 0)) =
          -μ (Sum.inr (Sum.inl ⟨g, hg⟩)) := by
        simp [mul_ite]
      have h_s4 : (∑ j : Fin n,
          (μ (Sum.inr (Sum.inr (Sum.inr (j, true)))) * (1 * g j) +
           μ (Sum.inr (Sum.inr (Sum.inr (j, false)))) * (-1 * g j))) = -(w ⬝ᵥ g) := by
        simp only [dotProduct, w, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h_s2, h_s4] at hg_eq
      have h_nonneg := hμ0 (Sum.inr (Sum.inl ⟨g, hg⟩))
      linarith
    have hw_xstar : γ < w ⬝ᵥ xstar := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, b_sys, sign_val,
        ↓reduceIte, Bool.false_eq_true, mul_zero, Finset.sum_const_zero, zero_add] at hμb
      have h_s4 : (∑ j : Fin n,
          (μ (Sum.inr (Sum.inr (Sum.inr (j, true)))) * (1 * xstar j) +
           μ (Sum.inr (Sum.inr (Sum.inr (j, false)))) * (-1 * xstar j))) = -(w ⬝ᵥ xstar) := by
        simp only [dotProduct, w, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h_s4] at hμb
      dsimp only [γ]
      linarith
    -- Every `z ∈ S_b` has `w ⬝ᵥ z ≤ γ`, so `w` has an IP optimal `z₀` on `S_b`
    have hw_Sb : ∀ z ∈ polyhedron A b, IsIntegral z → w ⬝ᵥ z ≤ γ := by
      intro z hzP hzI
      obtain ⟨z', hz'P, hz'I, hz'B, hzz'_cone⟩ := h_decomp z hzP hzI
      obtain ⟨k, g, c, hg, hc, hzz'_eq⟩ := hzz'_cone
      have hw_cone : w ⬝ᵥ (z - z') ≤ 0 := by
        rw [hzz'_eq, dot_sum_smul]
        exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hc j) (hw_Grec (g j) (hg j))
      have hw_z' : w ⬝ᵥ z' ≤ γ := hw_Fb ⟨z', hz'P, hz'I, hz'B⟩
      have : w ⬝ᵥ z = w ⬝ᵥ z' + w ⬝ᵥ (z - z') := by simp only [dotProduct_sub]; ring
      linarith
    obtain ⟨z₀, hz₀I, hz₀P, hz₀_opt⟩ :=
      exists_ip_optimal A b w ⟨x₀, hx₀P, hx₀I⟩ ⟨γ, hw_Sb⟩
    have hw_z₀_lt : w ⬝ᵥ z₀ < w ⬝ᵥ xstar := (hw_Sb z₀ hz₀P hz₀I).trans_lt hw_xstar
    -- Step 2: Replace `w` by an integral `w' ∈ RowsSet` separating `xstar` from `z₀`
    let K_step : ℤ := ((n * maxSubdet A : ℕ) : ℤ)
    let U₀ : Set (Fin n → ℤ) :=
      {u | (∀ j, |u j| ≤ K_step) ∧ z₀ + (fun j => (u j : ℚ)) ∈ polyhedron A b}
    have hU₀_fin : U₀.Finite := by
      refine (Set.finite_Icc (fun _ : Fin n => -K_step) (fun _ => K_step)).subset ?_
      intro u hu
      exact ⟨fun j => (abs_le.mp (hu.1 j)).1, fun j => (abs_le.mp (hu.1 j)).2⟩
    have : Fintype U₀ := hU₀_fin.fintype
    let m' := Fintype.card U₀
    let eU : Fin m' ≃ U₀ := (Fintype.equivFin U₀).symm
    let B_mat : Matrix (Fin m') (Fin n) ℤ := Matrix.of fun i j => (eU i).1 j
    have hBw : ∀ i : Fin m', ((B_mat.map (Int.cast : ℤ → ℚ)) *ᵥ w) i ≤ 0 := by
      intro i
      have huP : z₀ + (fun j => ((eU i).1 j : ℚ)) ∈ polyhedron A b := (eU i).2.2
      have huI : IsIntegral (z₀ + (fun j => ((eU i).1 j : ℚ))) :=
        isIntegral_add hz₀I (fun j => ⟨(eU i).1 j, rfl⟩)
      have h_le := hz₀_opt _ huP huI
      rw [dotProduct_add] at h_le
      have h_eq : ((B_mat.map (Int.cast : ℤ → ℚ)) *ᵥ w) i =
          w ⬝ᵥ (fun j => ((eU i).1 j : ℚ)) := by
        simp [B_mat, Matrix.mulVec, dotProduct, mul_comm]
      linarith
    have hex_w' : ∃ w' : Fin n → ℤ,
        (∀ j, |w' j| ≤ B_bound) ∧
        (∀ u ∈ U₀, (fun j => (w' j : ℚ)) ⬝ᵥ (fun j => (u j : ℚ)) ≤ 0) ∧
        (fun j => (w' j : ℚ)) ⬝ᵥ z₀ < (fun j => (w' j : ℚ)) ⬝ᵥ xstar := by
      by_cases hB0 : B_mat = 0
      · have hU₀_zero : ∀ u ∈ U₀, u = 0 := by
          intro u hu
          obtain ⟨i, hi⟩ := eU.surjective ⟨u, hu⟩
          ext j
          have := congrFun (congrFun hB0 i) j
          have h_apply : B_mat i j = u j := by
            dsimp only [B_mat, Matrix.of_apply]
            rw [hi]
          simpa [h_apply] using this
        have h_ne : xstar ≠ z₀ := fun h => by subst h; exact lt_irrefl _ hw_z₀_lt
        obtain ⟨j₀, hj₀⟩ : ∃ j, xstar j ≠ z₀ j := by
          by_contra h; push Not at h; exact h_ne (funext h)
        let sgn₀ : ℤ := if z₀ j₀ < xstar j₀ then 1 else -1
        let w' : Fin n → ℤ := fun j => if j = j₀ then sgn₀ else 0
        refine ⟨w', fun j => ?_, fun u hu => ?_, ?_⟩
        · dsimp only [w', sgn₀]
          split_ifs <;> simp only [abs_one, abs_neg, abs_zero] <;> linarith
        · rw [hU₀_zero u hu]
          simp
        · simp only [dotProduct, w', Int.cast_ite, Int.cast_zero, ite_mul, zero_mul,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          dsimp only [sgn₀]
          rcases lt_or_gt_of_ne hj₀ with hlt | hgt
          · rw [if_neg (not_lt.mpr hlt.le)]
            push_cast
            linarith
          · rw [if_pos hgt]
            push_cast
            linarith
      · obtain ⟨k, g, c, _, hgI, hgC, hgN, hc, hsum⟩ :=
          decomposition B_mat hB0 (fun _ => 1) (fun _ => one_ne_zero) w (fun i => by simpa using hBw i)
        have h_pos_sum : ∑ _l : Fin k, (0 : ℚ) < ∑ l : Fin k, c l * ((xstar - z₀) ⬝ᵥ g l) := by
          have h1 : (xstar - z₀) ⬝ᵥ w = ∑ l : Fin k, c l * ((xstar - z₀) ⬝ᵥ g l) := by
            rw [hsum, dot_sum_smul]
          have h_diff : 0 < (xstar - z₀) ⬝ᵥ w := by
            rw [dotProduct_comm, dotProduct_sub]
            linarith
          simp only [Finset.sum_const_zero]
          linarith
        obtain ⟨l₀, _, hl₀⟩ := Finset.exists_lt_of_sum_lt h_pos_sum
        have h_g_pos : 0 < (xstar - z₀) ⬝ᵥ g l₀ := by
          by_contra hle
          push Not at hle
          have := mul_nonpos_of_nonneg_of_nonpos (hc l₀) hle
          linarith
        choose w' hw' using hgI l₀
        have hw'_eq : g l₀ = fun j => (w' j : ℚ) := funext hw'
        have h_det_B : maxSubdet B_mat ≤ n ^ (2 * n) * maxSubdet A ^ n :=
          maxSubdet_le_of_entry_bound B_mat (maxSubdet A) (fun i j => (eU i).2.1 j)
        refine ⟨w', fun j => ?_, fun u hu => ?_, ?_⟩
        · have h1 : |(w' j : ℚ)| ≤ (maxSubdet B_mat : ℚ) := by
            rw [← hw' j]
            exact (abs_le_supNorm (g l₀) j).trans (hgN l₀)
          have h2 : (maxSubdet B_mat : ℚ) ≤ (B_bound : ℚ) := by
            dsimp only [B_bound]
            exact_mod_cast h_det_B
          exact_mod_cast h1.trans h2
        · obtain ⟨i, hi⟩ := eU.surjective ⟨u, hu⟩
          have h_le := hgC l₀ i
          simp only [one_mul, B_mat, Matrix.mulVec, dotProduct, Matrix.map_apply,
            Matrix.of_apply, hi, hw'_eq] at h_le
          simpa [dotProduct, mul_comm] using h_le
        · rw [← hw'_eq]
          rw [dotProduct_comm, dotProduct_sub] at h_g_pos
          linarith
    obtain ⟨w', hw'_bound, hw'_U₀, hw'_sep⟩ := hex_w'
    -- `w'` is in `RowsSet` because `G_rec A ⊆ U₀`
    have hw'_Grec : ∀ g ∈ G_rec A, (fun j => (w' j : ℚ)) ⬝ᵥ g ≤ 0 := by
      intro g hg
      choose u hu using hg.1
      have hu_mem : u ∈ U₀ := by
        refine ⟨fun j => ?_, ?_⟩
        · have h1 : |(u j : ℚ)| ≤ (maxSubdet A : ℚ) := by
            rw [← hu j]
            exact (abs_le_supNorm g j).trans hg.2.2
          have h2 : (maxSubdet A : ℚ) ≤ (K_step : ℚ) := by
            dsimp only [K_step]
            have : 1 * maxSubdet A ≤ n * maxSubdet A := Nat.mul_le_mul_right _ hn_pos
            simpa using (by exact_mod_cast this : ((1 * maxSubdet A : ℕ) : ℚ) ≤ ((n * maxSubdet A : ℕ) : ℚ))
          exact_mod_cast h1.trans h2
        · intro i
          have h_eq : (fun j => (u j : ℚ)) = g := funext fun j => (hu j).symm
          rw [h_eq, mulVec_add, Pi.add_apply]
          have h1 : ((A.map (Int.cast : ℤ → ℚ)) *ᵥ z₀) i ≤ b i := hz₀P i
          have h2 : ((A.map (Int.cast : ℤ → ℚ)) *ᵥ g) i ≤ 0 := hg.2.1 i
          linarith
      have h_eq : g = fun j => (u j : ℚ) := funext hu
      rw [h_eq]
      exact hw'_U₀ u hu_mem
    have hw'_mem : w' ∈ RowsSet := ⟨hw'_bound, hw'_Grec⟩
    obtain ⟨i₀, hi₀⟩ := eqv.surjective ⟨w', hw'_mem⟩
    have hM_i₀ : (fun j => (M i₀ j : ℚ)) = (fun j => (w' j : ℚ)) := by
      ext j
      dsimp only [M, Matrix.of_apply]
      rw [hi₀]
    -- By `improving_vector_small_core`, `z₀` is `w'`-optimal on `S_b`
    have hz₀_w'_opt : IsIPOptimal A b (fun j => (w' j : ℚ)) z₀ := by
      rcases improving_vector_small_core A hA b (fun j => (w' j : ℚ)) z₀ hz₀I hz₀P with
        hopt | ⟨zbar, hzbarI, hzbarP, hzbarB, hzbar_gt⟩
      · exact hopt
      · exfalso
        choose u hu using isIntegral_sub hzbarI hz₀I
        have hu_mem : u ∈ U₀ := by
          refine ⟨fun j => ?_, ?_⟩
          · have h1 : |(u j : ℚ)| ≤ (K_step : ℚ) := by
              rw [← hu j, Pi.sub_apply, abs_sub_comm]
              exact (abs_le_supNorm (z₀ - zbar) j).trans (by
                dsimp only [K_step]; push_cast; exact hzbarB)
            exact_mod_cast h1
          · have : z₀ + (fun j => (u j : ℚ)) = zbar := by
              ext j; simp [← hu j]
            rwa [this]
        have h_le := hw'_U₀ u hu_mem
        have h_eq : (fun j => (u j : ℚ)) = zbar - z₀ := funext fun j => (hu j).symm
        rw [h_eq, dotProduct_sub] at h_le
        linarith
    have hd_i₀_le : d i₀ ≤ (fun j => (w' j : ℚ)) ⬝ᵥ z₀ := by
      dsimp only [d]
      rw [hM_i₀]
      exact hz₀_w'_opt.2.2 (z_opt i₀) (hz_opt i₀).2.1 (hz_opt i₀).1
    have hxstar_le : (fun j => (w' j : ℚ)) ⬝ᵥ xstar ≤ d i₀ := by
      have h := hxstar i₀
      have h_eq : ((M.map (Int.cast : ℤ → ℚ)) *ᵥ xstar) i₀ = (fun j => (w' j : ℚ)) ⬝ᵥ xstar := by
        rw [← hM_i₀]
        simp [Matrix.mulVec, dotProduct]
      linarith
    linarith

end CookSensitivity.ChvatalRank

open CookSensitivity.ChvatalRank
open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin n) ℤ),
      (∀ i j, |M i j| ≤ ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℤ)) ∧
      ∀ b : Fin m → ℚ, (∃ x ∈ polyhedron A b, IsIntegral x) →
        ∃ d : Fin N → ℚ,
          integerHull (polyhedron A b) = {x | (M.map (Int.cast : ℤ → ℚ)) *ᵥ x ≤ d} :=
  integerHull_eq_of_bounded_matrix_core A
