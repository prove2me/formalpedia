-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_act_eq_comp_act_of_corr_of_isIsogenyPair_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/448f4629-a6c3-5e63-bf04-d3e637f78fa9

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_act_of_corr_of_isIsogenyPair_explicit

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem solution
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E Ef : FakeEllipticCurve Λ N B}
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef)

    (q : E.A ⟶ Ef.A) (q' : Ef.A ⟶ E.A) (Dq : ℕ) (hqq' : FakeEllipticCurve.IsIsogenyPair Dq E Ef q q')
    (f f' : A₀.A ⟶ A₀.A) (D : ℕ) (hff' : FakeEllipticCurve.IsIsogenyPair D A₀ A₀ f f')

    (qb : ρ.Eb.A ⟶ ρf.Eb.A) (hqb : qb ≫ ρf.gb = ρ.gb ≫ q) (hqbf : qb ≫ ρf.Eb.f = ρ.Eb.f)
    (uA : ρf.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (huAg : uA ≫ ρ.gA = ρf.gA)
    (eb : ρ.Ab.A ⟶ ρ.Ab.A) (heb : eb ≫ ρ.gA = ρ.gA ≫ f) (hebf : eb ≫ ρ.Ab.f = ρ.Ab.f)
    (i j : ℕ)
    (hP : qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ eb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (_ : f'b ≫ ρ.gA = ρ.gA ≫ f') (_ : f'b ≫ ρ.Ab.f = ρ.Ab.f),
      uA ≫ f'b ≫ ρ.φ' ≫ qb ≫ ρf.Eb.act ⟨(((Dq * r ^ (i + ρf.d) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        ρf.φ' ≫ ρf.Eb.act ⟨(((Dq * D * r ^ (j + ρ.d) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical

  have hmemN : ∀ k : ℕ, (((k : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun k => by exact_mod_cast hΛℤ (k : ℕ)
  have hcast : ∀ (k : ℕ) (h : ((((k : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (h' : (((k : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ),
      (⟨(((k : ℕ) : ℤ) : ℚ), h⟩ : ↥Λ) = ⟨((k : ℕ) : ℚ), h'⟩ := fun k h h' => Subtype.ext (by push_cast; rfl)
  have hmul : ∀ {S : Type} [CommRing S] (F : FakeEllipticCurve Λ N S) (p q : ℕ),
      F.act ⟨(((p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ F.act ⟨(((q : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        F.act ⟨((((q * p : ℕ)) : ℤ) : ℚ), hΛℤ _⟩ := by
    intro S _ F p q
    have hmem : ((⟨(((q : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) : ℍ[ℚ, a, b]) * ((⟨(((p : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by
      have := hΛℤ ((q : ℕ) * (p : ℕ) : ℤ)
      push_cast at this ⊢
      exact this
    rw [← F.act_mul _ _ hmem]
    congr 1
    apply Subtype.ext
    change ((((q : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((p : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) = ((((q * p : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b])
    norm_cast

  obtain ⟨hq₀, hq'₀, -, -, hqΛ, hq'Λ, hqcomp⟩ := hqq'
  obtain ⟨-, hq'q⟩ := hqcomp (hmemN Dq)
  obtain ⟨hf₀, hf'₀, -, -, hfΛ, hf'Λ, hfcomp⟩ := hff'
  obtain ⟨hff'c, -⟩ := hfcomp (hmemN D)
  obtain ⟨hgEb, -, hgbΛ, -⟩ := ρ.isPullback_Eb
  obtain ⟨hgEf, -, hgbfΛ, -⟩ := ρf.isPullback_Eb
  obtain ⟨hgA, -, hgAΛ, -⟩ := ρ.isPullback_Ab
  obtain ⟨-, -, huAΛ, -⟩ := huA
  obtain ⟨-, -, -, -, hφΛ, hφ'Λ, hφcomp⟩ := ρ.isIsogenyPair
  obtain ⟨hPP, -⟩ := hφcomp (hmemN (r ^ ρ.d))
  obtain ⟨hφf₀, -, -, -, hφfΛ, hφf'Λ, hφfcomp⟩ := ρf.isIsogenyPair
  obtain ⟨-, hPf⟩ := hφfcomp (hmemN (r ^ ρf.d))

  rw [← hcast Dq (hΛℤ _) (hmemN Dq)] at hq'q
  rw [← hcast D (hΛℤ _) (hmemN D)] at hff'c
  rw [← hcast (r ^ ρ.d) (hΛℤ _) (hmemN _)] at hPP
  rw [← hcast (r ^ ρf.d) (hΛℤ _) (hmemN _)] at hPf

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
  have hebf'b : eb ≫ f'b = ρ.Ab.act ⟨(((D : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    apply hgA.hom_ext
    · rw [Category.assoc, hf'b₁, ← Category.assoc, heb, Category.assoc, hff'c, hgAΛ]
    · rw [Category.assoc, hf'b₂, hebf, ρ.Ab.act_over]

  have hqbΛ : ∀ x : ↥Λ, ρ.Eb.act x ≫ qb = qb ≫ ρf.Eb.act x := by
    intro x
    apply hgEf.hom_ext
    · simp only [Category.assoc]
      rw [hqb, reassoc_of% (hgbΛ x), hqΛ x, hgbfΛ x, reassoc_of% hqb]
    · simp only [Category.assoc, hqbf, ρ.Eb.act_over, ρf.Eb.act_over]

  let q'b : ρf.Eb.A ⟶ ρ.Eb.A := hgEb.lift (ρf.gb ≫ q') ρf.Eb.f (by rw [Category.assoc, hq'₀]; exact hgEf.w)
  have hq'b₁ : q'b ≫ ρ.gb = ρf.gb ≫ q' := hgEb.lift_fst _ _ _
  have hq'b₂ : q'b ≫ ρ.Eb.f = ρf.Eb.f := hgEb.lift_snd _ _ _
  have hq'bqb : q'b ≫ qb = ρf.Eb.act ⟨(((Dq : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    apply hgEf.hom_ext
    · rw [Category.assoc, hqb, ← Category.assoc, hq'b₁, Category.assoc, hq'q, hgbfΛ]
    · rw [Category.assoc, hqbf, hq'b₂, ρf.Eb.act_over]

  refine ⟨f'b, hf'b₁, hf'b₂, ?_⟩

  have step1 := congrArg (fun κ => κ ≫ f'b ≫ ρ.φ' ≫ qb) hP
  simp only [Category.assoc] at step1
  rw [reassoc_of% (hf'bΛ ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% (hφ'Λ ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
    hqbΛ ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩] at step1
  rw [reassoc_of% (hf'bΛ ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% (hφ'Λ ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
    hqbΛ ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩, reassoc_of% hebf'b, reassoc_of% (hφ'Λ ⟨(((D : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
    reassoc_of% (hqbΛ ⟨(((D : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% hPP, reassoc_of% (hqbΛ _), hmul, hmul] at step1

  have step2 := congrArg (fun κ => ρf.φ' ≫ q'b ≫ κ) step1
  rw [reassoc_of% hq'bqb, reassoc_of% hq'bqb, reassoc_of% (hφfΛ _), reassoc_of% hPf, hmul] at step2

  rw [reassoc_of% (huAΛ ⟨(((Dq : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% (hf'bΛ ⟨(((Dq : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
    reassoc_of% (hφ'Λ ⟨(((Dq : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% (hqbΛ ⟨(((Dq : ℕ) : ℤ) : ℚ), hΛℤ _⟩), hmul,
    reassoc_of% (huAΛ ⟨(((r ^ ρf.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% (hf'bΛ ⟨(((r ^ ρf.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
    reassoc_of% (hφ'Λ ⟨(((r ^ ρf.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% (hqbΛ ⟨(((r ^ ρf.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩), hmul] at step2
  have key : uA ≫ f'b ≫ ρ.φ' ≫ qb ≫ ρf.Eb.act ⟨(((r ^ i * Dq * r ^ ρf.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ρf.φ' ≫ ρf.Eb.act ⟨(((r ^ j * D * r ^ ρ.d * Dq : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := step2
  have n1 : r ^ i * Dq * r ^ ρf.d = Dq * r ^ (i + ρf.d) := by ring
  have n2 : r ^ j * D * r ^ ρ.d * Dq = Dq * D * r ^ (j + ρ.d) := by ring
  have e1 : (⟨(((r ^ i * Dq * r ^ ρf.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨(((Dq * r ^ (i + ρf.d) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ :=
    Subtype.ext (by simp only [n1])
  have e2 : (⟨(((r ^ j * D * r ^ ρ.d * Dq : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨(((Dq * D * r ^ (j + ρ.d) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ :=
    Subtype.ext (by simp only [n2])
  rw [e1, e2] at key
  exact key

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_act_of_corr_of_isIsogenyPair_explicit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_act_eq_comp_act_of_corr_of_isIsogenyPair_explicit (solution)
