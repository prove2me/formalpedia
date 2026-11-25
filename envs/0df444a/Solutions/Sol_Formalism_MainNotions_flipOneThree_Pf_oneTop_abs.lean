-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.oneTop_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:38:19.185813+00:00
-- url     : https://prove2.me/submissions/e5158481-078d-4819-b581-4cce9d69a8a2

import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_HarProjEqZeroIff
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_smul_mem_latOf
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_harProj_eq_zero_iff
import Theorems.Thm_Formalism_CountingSumsFrames_Top_gaussLemmaH
import Theorems.Thm_Formalism_CountingSumsFrames_Top_gaussProj
import Theorems.Thm_Formalism_CountingSumsFrames_Top_harProj
import Theorems.Thm_Formalism_CountingSumsFrames_Top_levelLattice
import Theorems.Thm_Formalism_CountingSumsFrames_Top_levelProj
import Theorems.Thm_Formalism_CountingSumsFrames_Top_slTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.flipOneThree.Pf
open Formalism.CountingSumsFrames MvPolynomial
private theorem mem_PolAB_iff_xDeg_yDeg {K : Type} [Field K] {k A B : ℕ} {f : Formalism.CountingSumsFrames.PolXY K k} :
    f ∈ Formalism.CountingSumsFrames.PolAB K k A B ↔ ∀ m ∈ f.support, Formalism.CountingSumsFrames.xDeg m = A ∧ Formalism.CountingSumsFrames.yDeg m = B := Iff.rfl
private theorem mul_mem_PolAB_add {K : Type} [Field K] {k A B C E : ℕ} {f g : Formalism.CountingSumsFrames.PolXY K k}
    (hf : f ∈ Formalism.CountingSumsFrames.PolAB K k A B) (hg : g ∈ Formalism.CountingSumsFrames.PolAB K k C E) :
    f * g ∈ Formalism.CountingSumsFrames.PolAB K k (A + C) (B + E) := by
  classical
  rw [mem_PolAB_iff_xDeg_yDeg] at hf hg ⊢
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  obtain ⟨h1, h2⟩ := hf a ha
  obtain ⟨h3, h4⟩ := hg b hb
  constructor
  · simp only [Formalism.CountingSumsFrames.xDeg, Finsupp.add_apply, Finset.sum_add_distrib] at h1 h3 ⊢
    rw [h1, h3]
  · simp only [Formalism.CountingSumsFrames.yDeg, Finsupp.add_apply, Finset.sum_add_distrib] at h2 h4 ⊢
    rw [h2, h4]
private theorem X_inl_mem_PolAB_one_zero {K : Type} [Field K] {k : ℕ} (i : Fin k) :
    (X (Sum.inl i) : Formalism.CountingSumsFrames.PolXY K k) ∈ Formalism.CountingSumsFrames.PolAB K k 1 0 := by
  rw [mem_PolAB_iff_xDeg_yDeg]
  intro m hm
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  simp [Formalism.CountingSumsFrames.xDeg, Formalism.CountingSumsFrames.yDeg, Finsupp.single_apply]
private theorem X_inr_mem_PolAB_zero_one {K : Type} [Field K] {k : ℕ} (i : Fin k) :
    (X (Sum.inr i) : Formalism.CountingSumsFrames.PolXY K k) ∈ Formalism.CountingSumsFrames.PolAB K k 0 1 := by
  rw [mem_PolAB_iff_xDeg_yDeg]
  intro m hm
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  simp [Formalism.CountingSumsFrames.xDeg, Formalism.CountingSumsFrames.yDeg, Finsupp.single_apply]
private theorem hXY_mem_PolAB_one_one {K : Type} [Field K] {k : ℕ} : Formalism.CountingSumsFrames.hXY K k ∈ Formalism.CountingSumsFrames.PolAB K k 1 1 := by
  unfold Formalism.CountingSumsFrames.hXY
  refine Submodule.sum_mem _ (fun i _ => ?_)
  exact mul_mem_PolAB_add (X_inl_mem_PolAB_one_zero (K := K) i) (X_inr_mem_PolAB_zero_one i)
private theorem hXY_pow_mem_PolAB {K : Type} [Field K] {k : ℕ} (j : ℕ) :
    Formalism.CountingSumsFrames.hXY K k ^ j ∈ Formalism.CountingSumsFrames.PolAB K k j j := by
  induction j with
  | zero =>
    rw [pow_zero, mem_PolAB_iff_xDeg_yDeg]
    intro m hm
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp [Formalism.CountingSumsFrames.xDeg, Formalism.CountingSumsFrames.yDeg]
    · exact (hm rfl).elim
  | succ n ih =>
    rw [pow_succ]
    exact mul_mem_PolAB_add ih hXY_mem_PolAB_one_one
end Formalism.MainNotions.flipOneThree.Pf
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf
open Formalism.CountingSumsFrames MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf
theorem _root_.solution (K : Type) [Field K] [CharZero K] (k P Q p : ℕ) (hk : 1 ≤ k) (hp : p.Prime)
    (Ov : ValuationSubring K) (hloc : PLocal Ov.toSubring p)
    {V2 : Type} [AddCommGroup V2] [Module K V2] (α : V2 ≃ₗ[K] PolAB K k P Q)
    (W : ℕ → Type) [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    (β : ∀ j, PolAB K k (P - j) (Q - j) →ₗ[K] W j) (hsurj : ∀ j, Function.Surjective (β j))
    (hker : ∀ j (f : PolAB K k (P - j) (Q - j)), β j f = 0 ↔
      ∃ G ∈ PolAB K k (P - j - 1) (Q - j - 1), (f : PolXY K k) = hXY K k * G) :
    ∃ (io : ∀ j, W j →ₗ[K] V2) (pr : ∀ j, V2 →ₗ[K] W j),
      (∀ x, ∑ j ∈ Finset.range (min P Q + 1), io j (pr j x) = x) ∧
      ∀ (g : GL (Fin k) K) (j : ℕ), j ≤ min P Q →
        (∀ x, (α x : PolXY K k) ∈ latOf g (GaussLat Ov.toSubring) →
          ∃ f : PolAB K k (P - j) (Q - j), (f : PolXY K k) ∈ latOf g (GaussLat Ov.toSubring) ∧
            β j f = ((p : K) ^ ((k + 1) * Nat.log p (P + Q + k))) • pr j x) ∧
        (∀ f : PolAB K k (P - j) (Q - j), (f : PolXY K k) ∈ latOf g (GaussLat Ov.toSubring) →
          (α (((p : K) ^ ((k + 1) * Nat.log p (P + Q + k))) • io j (β j f)) : PolXY K k) ∈
            latOf g (GaussLat Ov.toSubring)) := by
  classical
  have HP : Formalism.CountingSumsFrames.HarProj := Formalism.CountingSumsFrames.Top.harProj
  have IP : Formalism.CountingSumsFrames.LevelProj := Formalism.CountingSumsFrames.Top.levelProj
  have GP : Formalism.CountingSumsFrames.GaussProj := Formalism.CountingSumsFrames.Top.gaussProj
  have GLP : Formalism.CountingSumsFrames.GaussLemmaH := Formalism.CountingSumsFrames.Top.gaussLemmaH
  have IL : Formalism.CountingSumsFrames.LevelLattice := Formalism.CountingSumsFrames.Top.levelLattice
  have SC : Formalism.CountingSumsFrames.SlTwo := Formalism.CountingSumsFrames.Top.slTwo
  have hpair : Formalism.CountingSumsFrames.hXY K k ≠ 0 := by
    intro h0
    have h1 : (1 : Formalism.CountingSumsFrames.PolXY K k) ∈ Formalism.CountingSumsFrames.PolAB K k 0 0 := by
      simpa using hXY_pow_mem_PolAB (K := K) (k := k) 0
    have h2 := SC K k 0 0 1 h1
    rw [h0] at h2
    simp only [zero_mul, map_zero, sub_self, zero_add] at h2
    have h3 : ((k : ℕ) : K) = 0 := by
      have h4 := congrArg (MvPolynomial.coeff 0) h2.symm
      simpa using h4
    exact absurd (Nat.cast_eq_zero.1 h3) (by omega)
  have hle : ∀ A B, Formalism.CountingSumsFrames.HarAB K k A B ≤ Formalism.CountingSumsFrames.PolAB K k A B := fun A B => inf_le_left
  let D : ℕ → Formalism.CountingSumsFrames.PolXY K k →ₗ[K] Formalism.CountingSumsFrames.PolXY K k := fun j =>
    ((((P + Q + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹ * ((j.factorial : K))⁻¹) •
      (Formalism.CountingSumsFrames.harProj K k (P - j) (Q - j) ∘ₗ Formalism.CountingSumsFrames.ctrDiv K k j)
  have hD : ∀ j F, Formalism.CountingSumsFrames.levelProj K k P Q j F = Formalism.CountingSumsFrames.hXY K k ^ j * D j F := by
    intro j F
    simp only [D, Formalism.CountingSumsFrames.levelProj, Formalism.CountingSumsFrames.hDiv, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply]
    rw [mul_smul_comm, smul_smul]
  have hDmem : ∀ j, j ≤ min P Q → ∀ F ∈ Formalism.CountingSumsFrames.PolAB K k P Q,
      D j F ∈ Formalism.CountingSumsFrames.HarAB K k (P - j) (Q - j) := by
    intro j hj F hF
    obtain ⟨w, hw, hw'⟩ := (IP K k P Q hk).1 F hF j hj
    rw [hD] at hw'
    rw [mul_left_cancel₀ (pow_ne_zero j hpair) hw']
    exact hw
  have hjP : ∀ j, j ≤ min P Q → j ≤ P := fun j hj => le_trans hj (min_le_left _ _)
  have hjQ : ∀ j, j ≤ min P Q → j ≤ Q := fun j hj => le_trans hj (min_le_right _ _)
  let Dc : ∀ j, j ≤ min P Q → V2 →ₗ[K] Formalism.CountingSumsFrames.PolAB K k (P - j) (Q - j) := fun j hj =>
    LinearMap.codRestrict _ (D j ∘ₗ (Formalism.CountingSumsFrames.PolAB K k P Q).subtype ∘ₗ α.toLinearMap)
      (fun x => hle _ _ (hDmem j hj _ (α x).2))
  have hEmem : ∀ j, j ≤ min P Q → ∀ f : Formalism.CountingSumsFrames.PolAB K k (P - j) (Q - j),
      Formalism.CountingSumsFrames.hXY K k ^ j * Formalism.CountingSumsFrames.harProj K k (P - j) (Q - j) f ∈ Formalism.CountingSumsFrames.PolAB K k P Q := by
    intro j hj f
    have h := mul_mem_PolAB_add (hXY_pow_mem_PolAB (K := K) (k := k) j)
      (hle _ _ ((HP K k (P - j) (Q - j) hk).1 f f.2).1)
    rwa [Nat.add_sub_of_le (hjP j hj), Nat.add_sub_of_le (hjQ j hj)] at h
  let E : ∀ j, j ≤ min P Q → Formalism.CountingSumsFrames.PolAB K k (P - j) (Q - j) →ₗ[K] V2 := fun j hj =>
    α.symm.toLinearMap ∘ₗ LinearMap.codRestrict _
      (LinearMap.mulLeft K (Formalism.CountingSumsFrames.hXY K k ^ j) ∘ₗ Formalism.CountingSumsFrames.harProj K k (P - j) (Q - j) ∘ₗ
        (Formalism.CountingSumsFrames.PolAB K k (P - j) (Q - j)).subtype) (fun f => hEmem j hj f)
  choose s hs using fun j =>
    LinearMap.exists_rightInverse_of_surjective (β j) (LinearMap.range_eq_top.2 (hsurj j))
  have hβs : ∀ j w, β j (s j w) = w := fun j w => LinearMap.congr_fun (hs j) w
  have hEcoe : ∀ j (hj : j ≤ min P Q) f,
      ((α (E j hj f) : Formalism.CountingSumsFrames.PolAB K k P Q) : Formalism.CountingSumsFrames.PolXY K k) =
        Formalism.CountingSumsFrames.hXY K k ^ j * Formalism.CountingSumsFrames.harProj K k (P - j) (Q - j) f := by
    intro j hj f
    simp only [E, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have hEker : ∀ j (hj : j ≤ min P Q) f, β j f = 0 → E j hj f = 0 := by
    intro j hj f h0
    apply α.injective
    apply Subtype.ext
    rw [hEcoe j hj, (harProj_eq_zero_iff hk p hp Ov hloc f.2).2 ((hker j f).1 h0)]
    simp
  have hEβ : ∀ j (hj : j ≤ min P Q) f, E j hj (s j (β j f)) = E j hj f := by
    intro j hj f
    have h := hEker j hj (s j (β j f) - f) (by rw [map_sub, hβs, sub_self])
    rwa [map_sub, sub_eq_zero] at h
  let pr : ∀ j, V2 →ₗ[K] W j := fun j =>
    if hj : j ≤ min P Q then β j ∘ₗ Dc j hj else 0
  let io : ∀ j, W j →ₗ[K] V2 := fun j =>
    if hj : j ≤ min P Q then E j hj ∘ₗ s j else 0
  have hpr : ∀ j (hj : j ≤ min P Q) x, pr j x = β j (Dc j hj x) := by
    intro j hj x
    simp only [pr, dif_pos hj, LinearMap.comp_apply]
  have hio : ∀ j (hj : j ≤ min P Q) f, io j (β j f) = E j hj f := by
    intro j hj f
    simp only [io, dif_pos hj, LinearMap.comp_apply]
    exact hEβ j hj f
  have hterm : ∀ j (hj : j ≤ min P Q) x,
      ((α (io j (pr j x)) : Formalism.CountingSumsFrames.PolAB K k P Q) : Formalism.CountingSumsFrames.PolXY K k) =
        Formalism.CountingSumsFrames.levelProj K k P Q j (α x) := by
    intro j hj x
    rw [hpr j hj, hio j hj, hEcoe j hj]
    have hDc : ((Dc j hj x : Formalism.CountingSumsFrames.PolAB K k (P - j) (Q - j)) : Formalism.CountingSumsFrames.PolXY K k) = D j (α x) := rfl
    rw [hDc, (HP K k (P - j) (Q - j) hk).2.1 _ (hDmem j hj _ (α x).2), hD]
  refine ⟨io, pr, ?_, ?_⟩
  · intro x
    apply α.injective
    apply Subtype.ext
    rw [map_sum, Submodule.coe_sum,
      Finset.sum_congr rfl (fun j hj => hterm j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x)]
    exact (IP K k P Q hk).2.1 _ (α x).2
  · intro g j hj
    refine ⟨fun x hx => ?_, fun f hf => ?_⟩
    · refine ⟨((p : K) ^ ((k + 1) * Nat.log p (P + Q + k))) • Dc j hj x, ?_, ?_⟩
      · apply GLP K k Ov g j _ hk
        have h := ((GP K k P Q p Ov.toSubring g hk hp hloc (α x) (α x).2).1 hx).2 j hj
        rw [hD, ← mul_smul_comm] at h
        rw [Submodule.coe_smul]
        exact h
      · rw [map_smul, hpr j hj]
    · have hw : ((p : K) ^ ((k + 1) * Nat.log p (P + Q + k))) •
          Formalism.CountingSumsFrames.harProj K k (P - j) (Q - j) f ∈ Formalism.CountingSumsFrames.HarAB K k (P - j) (Q - j) :=
        Submodule.smul_mem _ _ ((HP K k (P - j) (Q - j) hk).1 f f.2).1
      have he : (k + 1) * Nat.log p (P - j + (Q - j) + k) ≤ (k + 1) * Nat.log p (P + Q + k) :=
        Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))
      have hL : ((p : K) ^ ((k + 1) * Nat.log p (P + Q + k))) •
          Formalism.CountingSumsFrames.harProj K k (P - j) (Q - j) f ∈ Formalism.CountingSumsFrames.latOf g (Formalism.CountingSumsFrames.GaussLat Ov.toSubring) := by
        have h0 := ((GP K k (P - j) (Q - j) p Ov.toSubring g hk hp hloc f f.2).1 hf).1
        have h1 := smul_mem_latOf Ov.toSubring g
          (pow_mem (natCast_mem Ov.toSubring p)
            ((k + 1) * Nat.log p (P + Q + k) - (k + 1) * Nat.log p (P - j + (Q - j) + k))) h0
        rwa [smul_smul, ← pow_add, Nat.sub_add_cancel he] at h1
      have hmem : Formalism.CountingSumsFrames.hXY K k ^ j * (((p : K) ^ ((k + 1) * Nat.log p (P + Q + k))) •
          Formalism.CountingSumsFrames.harProj K k (P - j) (Q - j) f) ∈
          (fun w => Formalism.CountingSumsFrames.hXY K k ^ j * w) '' (Formalism.CountingSumsFrames.latOf g (Formalism.CountingSumsFrames.GaussLat Ov.toSubring) ∩
            (Formalism.CountingSumsFrames.HarAB K k (P - j) (Q - j) : Set (Formalism.CountingSumsFrames.PolXY K k))) :=
        ⟨_, ⟨hL, hw⟩, rfl⟩
      rw [← IL K k (P - j) (Q - j) j Ov g hk] at hmem
      rw [map_smul, hio j hj, Submodule.coe_smul, hEcoe j hj, ← mul_smul_comm]
      exact hmem.1
end Formalism.MainNotions.flipOneThree.Pf
