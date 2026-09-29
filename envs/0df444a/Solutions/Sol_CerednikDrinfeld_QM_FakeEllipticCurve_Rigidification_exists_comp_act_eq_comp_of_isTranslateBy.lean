-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_act_eq_comp_of_isTranslateBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/81f374c5-9200-5bfd-a880-0f208dab3cf3

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_of_isTranslateBy

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem solution
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ρ ρ' : Rigidification r π A₀ ψ E) (f f' : A₀.A ⟶ A₀.A) (dγ : ℕ)
    (hff' : FakeEllipticCurve.IsIsogenyPair (r ^ dγ) A₀ A₀ f f') (htr : Rigidification.IsTranslateBy hΛℤ f ρ ρ') :
    ∃ (u : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : Rigidification.IsComparison ρ ρ' u uA)
      (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (_ : f'b ≫ ρ.gA = ρ.gA ≫ f') (_ : f'b ≫ ρ.Ab.f = ρ.Ab.f) (i j : ℕ),
      ρ'.φ' ≫ u ≫ ρ.Eb.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        uA ≫ f'b ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  have hmemN : ∀ k : ℕ, (((r ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun k => by exact_mod_cast hΛℤ (r ^ k : ℕ)
  have hcast : ∀ (k : ℕ) (h : ((((r ^ k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (h' : (((r ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ),
      (⟨(((r ^ k : ℕ) : ℤ) : ℚ), h⟩ : ↥Λ) = ⟨((r ^ k : ℕ) : ℚ), h'⟩ := fun k h h' => Subtype.ext (by push_cast; rfl)
  have hmul : ∀ {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) (p q : ℕ),
      F.act ⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ F.act ⟨(((r ^ q : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        F.act ⟨(((r ^ (p + q) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    intro S _ F p q
    have hmem : ((⟨(((r ^ q : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨(((r ^ p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by
      have := hΛℤ ((r ^ q : ℕ) * (r ^ p : ℕ) : ℤ)
      push_cast at this ⊢
      exact this
    rw [← F.act_mul _ _ hmem]
    congr 1
    apply Subtype.ext
    push_cast
    rw [add_comm p q, pow_add]

  obtain ⟨u, uA, hcmp, fb, hfb₁, hfb₂, i, j, hrel⟩ := htr
  have hcmp' := hcmp
  obtain ⟨⟨hgEb, -, huΛ, -⟩, hugb, ⟨hguA, -, huAΛ, -⟩, hugA⟩ := hcmp'
  obtain ⟨hf₀, hf'₀, -, -, hfΛ, hf'Λ, hcomp⟩ := hff'
  obtain ⟨hc₁, -⟩ := hcomp (hmemN dγ)
  obtain ⟨hgA, -, hgAΛ, -⟩ := ρ.isPullback_Ab
  obtain ⟨hφ₀, hφ'₀, -, -, hφΛ, hφ'Λ, hφcomp⟩ := ρ.isIsogenyPair
  obtain ⟨hP, -⟩ := hφcomp (hmemN ρ.d)
  obtain ⟨-, -, -, -, -, -, hφcomp'⟩ := ρ'.isIsogenyPair
  obtain ⟨-, hP'⟩ := hφcomp' (hmemN ρ'.d)

  let f'b : ρ.Ab.A ⟶ ρ.Ab.A := hgA.lift (ρ.gA ≫ f') ρ.Ab.f (by rw [Category.assoc, hf'₀]; exact hgA.w)
  have hf'b₁ : f'b ≫ ρ.gA = ρ.gA ≫ f' := hgA.lift_fst _ _ _
  have hf'b₂ : f'b ≫ ρ.Ab.f = ρ.Ab.f := hgA.lift_snd _ _ _

  have hf'bΛ : ∀ x : ↥Λ, ρ.Ab.act x ≫ f'b = f'b ≫ ρ.Ab.act x := by
    intro x
    apply hgA.hom_ext
    · have l : (ρ.Ab.act x ≫ f'b) ≫ ρ.gA = ρ.gA ≫ f' ≫ A₀.act x := by
        rw [Category.assoc, hf'b₁, ← Category.assoc, hgAΛ x, Category.assoc, hf'Λ x]
      have r' : (f'b ≫ ρ.Ab.act x) ≫ ρ.gA = ρ.gA ≫ f' ≫ A₀.act x := by
        rw [Category.assoc, hgAΛ x, ← Category.assoc, hf'b₁, Category.assoc]
      exact l.trans r'.symm
    · simp only [Category.assoc, hf'b₂, ρ.Ab.act_over]
  have hfbf'b : fb ≫ f'b = ρ.Ab.act ⟨(((r ^ dγ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    apply hgA.hom_ext
    · rw [Category.assoc, hf'b₁, ← Category.assoc, hfb₁, Category.assoc, hc₁, ← hcast dγ (hΛℤ _) (hmemN dγ),
        hgAΛ]
    · rw [Category.assoc, hf'b₂, hfb₂, ρ.Ab.act_over]

  have hP'' : ρ'.φ' ≫ ρ'.φ = ρ'.Ab.act ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [hP', ← hcast ρ'.d (hΛℤ _) (hmemN ρ'.d)]
  have hPP : ρ.φ ≫ ρ.φ' = ρ.Eb.act ⟨(((r ^ ρ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [hP, ← hcast ρ.d (hΛℤ _) (hmemN ρ.d)]
  refine ⟨u, uA, hcmp, f'b, hf'b₁, hf'b₂, ρ.d + (dγ + i), ρ'.d + j, ?_⟩

  have step1 : ρ'.φ' ≫ u ≫ ρ.φ ≫ fb ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      uA ≫ ρ.Ab.act ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    calc ρ'.φ' ≫ u ≫ ρ.φ ≫ fb ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩
        = ρ'.φ' ≫ (ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by rw [← hrel]
      _ = (ρ'.φ' ≫ ρ'.φ) ≫ uA ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
      _ = uA ≫ ρ.Ab.act ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          rw [hP'', ← Category.assoc, huAΛ, Category.assoc]
  have step2 := congrArg (fun κ => κ ≫ f'b ≫ ρ.φ') step1
  simp only [Category.assoc] at step2

  have L : ρ'.φ' ≫ u ≫ ρ.φ ≫ fb ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ f'b ≫ ρ.φ' =
      ρ'.φ' ≫ u ≫ ρ.Eb.act ⟨(((r ^ (ρ.d + (dγ + i)) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [reassoc_of% (hf'bΛ ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% hfbf'b,
      hφ'Λ ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩, reassoc_of% (hφ'Λ ⟨(((r ^ dγ : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
      reassoc_of% hPP, hmul, hmul]

  have R : uA ≫ ρ.Ab.act ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ f'b ≫ ρ.φ' =
      uA ≫ f'b ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ (ρ'.d + j) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [reassoc_of% (hf'bΛ ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
      reassoc_of% (hf'bΛ ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
      hφ'Λ ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩, reassoc_of% (hφ'Λ ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩), hmul]
  rw [← L, ← R]
  exact step2

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_of_isTranslateBy
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_of_isTranslateBy (solution)
