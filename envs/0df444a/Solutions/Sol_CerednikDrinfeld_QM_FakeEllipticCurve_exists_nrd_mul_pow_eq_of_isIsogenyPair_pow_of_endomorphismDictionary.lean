-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_nrd_mul_pow_eq_of_isIsogenyPair_pow_of_endomorphismDictionary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4c01839a-fafc-5eca-bd34-9b015ba6f1a4

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_nrd_mul_pow_eq_pow_of_mem_awayUnits
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nrd_mul_pow_eq_of_isIsogenyPair_pow_of_endomorphismDictionary

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem solution
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {N : ℕ}
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (A₀ : FakeEllipticCurve Λ N k₀)
    {a₁ b₁ : ℚ} (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (e : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f)

    (hE4 : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra k₀ k]
        (A : FakeEllipticCurve Λ N k) (gA : A.A ⟶ A₀.A),
        FakeEllipticCurve.IsPullbackVia (algebraMap k₀ k) A₀ A gA →
        (∀ (φ ψ : A.A ⟶ A.A) (d : ℕ) (hφ : φ ≫ A.f = A.f),
            FakeEllipticCurve.IsIsogenyPair (r ^ d) A A φ ψ → FakeEllipticCurve.PreservesLevel A A φ hφ →
            ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ A.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ gA = gA ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

    (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁)
    (hR₂r : ∀ x : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (x : ℍ[ℚ, a₁, b₁]) ∈ R₂)
    (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ x, ê x ≫ A₀.f = A₀.f)
    (hE5lev : ∀ x : ↥R₂, FakeEllipticCurve.PreservesLevel A₀ A₀ (ê x) (hê x))
    (hE5mul : ∀ (x y : ↥R₂) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
      ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê x)
    (hE5int : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)
    (hE5d : ∀ (γ : ↥Γt) (x : ↥R₂) (k : ℕ),
      (x : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
      ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê x ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hinj : ∀ x y : ↥R₂, ê x = ê y → x = y) :
    ∀ (z : ↥R₂) (ψ : A₀.A ⟶ A₀.A) (j : ℕ), FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ (ê z) ψ →
      ∃ i t : ℕ, nrd (z : ℍ[ℚ, a₁, b₁]) * ((r : ℚ) ^ i) = (r : ℚ) ^ t ∨ nrd (z : ℍ[ℚ, a₁, b₁]) * ((r : ℚ) ^ i) = -((r : ℚ) ^ t) := by
  classical
  intro z ψ j hpair
  have hr : r.Prime := Fact.out

  have hQ : ∀ m n : ℕ,
      A₀.act ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ A₀.act ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        A₀.act ⟨(((r ^ (m + n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    intro m n
    have hval : (((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b])) =
        ((((r ^ (m + n) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
      rw [← QuaternionAlgebra.coe_mul]; congr 1; push_cast; ring
    have hmem : (((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b])) ∈ Λ := hval ▸ hΛℤ _
    rw [← A₀.act_mul ⟨_, hΛℤ _⟩ ⟨_, hΛℤ _⟩ hmem]
    congr 1; exact Subtype.ext hval

  have hpb : FakeEllipticCurve.IsPullbackVia (algebraMap k₀ k₀) A₀ A₀ (𝟙 A₀.A) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id k₀ A₀
  obtain ⟨γ, i, j', hE⟩ := hE4 k₀ A₀ (𝟙 A₀.A) hpb (ê z) ψ j (hê z) hpair (hE5lev z)
  simp only [Category.comp_id, Category.id_comp] at hE

  obtain ⟨hiff, -⟩ := CerednikDrinfeld.CosetGraph.mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq R₁ R₁ hR₁ hR₁ r v hv (fun _ _ => rfl)
  obtain ⟨K, K', hK, -⟩ := (hiff (γ : (ℍ[ℚ, a₁, b₁])ˣ)).mp ((hΓt _).mp γ.2)
  obtain ⟨c, hc⟩ := hR₂r ⟨_, hK⟩
  obtain ⟨x, hxR⟩ : ∃ x : ↥R₂, (x : ℍ[ℚ, a₁, b₁]) = ((r ^ c : ℕ) : ℚ) • (((r ^ K : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) :=
    ⟨⟨_, hc⟩, rfl⟩
  have hxval : (x : ℍ[ℚ, a₁, b₁]) = ((r ^ (c + K) : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) := by
    rw [hxR, smul_smul]; congr 1; push_cast; ring
  obtain ⟨i', j'', hD⟩ := hE5d γ x (c + K) hxval

  have hcomb : ê z ≫ A₀.act ⟨(((r ^ (i + i') : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ê x ≫ A₀.act ⟨(((r ^ (j'' + j') : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    calc ê z ≫ A₀.act ⟨(((r ^ (i + i') : ℕ) : ℤ) : ℚ), hΛℤ _⟩
        = (ê z ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ A₀.act ⟨(((r ^ i' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          rw [Category.assoc, hQ]
      _ = (e γ ≫ A₀.act ⟨(((r ^ j' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ A₀.act ⟨(((r ^ i' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hE]
      _ = (e γ ≫ A₀.act ⟨(((r ^ i' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ A₀.act ⟨(((r ^ j' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          rw [Category.assoc, Category.assoc, hQ, hQ, Nat.add_comm]
      _ = (ê x ≫ A₀.act ⟨(((r ^ j'' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ A₀.act ⟨(((r ^ j' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [hD]
      _ = ê x ≫ A₀.act ⟨(((r ^ (j'' + j') : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [Category.assoc, hQ]

  obtain ⟨c₀, hc₀⟩ := hR₂r ⟨1, hR₁.one_mem⟩
  have hpow_mem : ∀ n : ℕ, ((((r ^ (n + c₀) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂ := by
    intro n
    have h1 : ((((r ^ (n + c₀) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) = ((r ^ n : ℕ) : ℤ) • (((r ^ c₀ : ℕ) : ℚ) • ((⟨1, hR₁.one_mem⟩ : ↥R₁) : ℍ[ℚ, a₁, b₁])) := by
      rw [zsmul_eq_mul, Submodule.coe_mk, Algebra.smul_def, mul_one]; push_cast; rw [← pow_add]
    rw [h1]; exact R₂.smul_mem _ hc₀
  have hmul_mem : ∀ (n : ℕ) (w : ↥R₂), ((((r ^ (n + c₀) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) * (w : ℍ[ℚ, a₁, b₁]) ∈ R₂ := by
    intro n w
    have h1 : ((((r ^ (n + c₀) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) * (w : ℍ[ℚ, a₁, b₁]) = ((r ^ (n + c₀) : ℕ) : ℤ) • (w : ℍ[ℚ, a₁, b₁]) := by
      rw [zsmul_eq_mul]; norm_cast
    rw [h1]; exact R₂.smul_mem _ w.2
  have hfold : ∀ (n : ℕ) (w : ↥R₂),
      ê w ≫ A₀.act ⟨(((r ^ (n + c₀) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê ⟨_, hmul_mem n w⟩ := by
    intro n w
    rw [hE5mul ⟨_, hpow_mem n⟩ w (hmul_mem n w), hE5int _ (hpow_mem n)]

  have hcomb2 : ê z ≫ A₀.act ⟨(((r ^ (i + i' + c₀) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ê x ≫ A₀.act ⟨(((r ^ (j'' + j' + c₀) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [← hQ (i + i') c₀, ← hQ (j'' + j') c₀, ← Category.assoc, ← Category.assoc, hcomb]
  have hcomb' : ê ⟨_, hmul_mem (i + i') z⟩ = ê ⟨_, hmul_mem (j'' + j') x⟩ := by
    rw [← hfold, ← hfold]; exact hcomb2
  have heq : ((((r ^ (i + i' + c₀) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) * (z : ℍ[ℚ, a₁, b₁]) =
      ((((r ^ (j'' + j' + c₀) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a₁, b₁]) * (x : ℍ[ℚ, a₁, b₁]) :=
    congrArg Subtype.val (hinj _ _ hcomb')

  obtain ⟨i₀, j₀, hγ⟩ := CerednikDrinfeld.CosetGraph.exists_nrd_mul_pow_eq_pow_of_mem_awayUnits R₁ hR₁ r v hv (γ : (ℍ[ℚ, a₁, b₁])ˣ) ((hΓt _).mp γ.2)
  have hn := congrArg nrd heq
  rw [hxval] at hn

  have hsm : ∀ (q : ℚ) (y : ℍ[ℚ, a₁, b₁]), ((q : ℚ) : ℍ[ℚ, a₁, b₁]) * y = q • y := fun q y => (Algebra.smul_def q y).symm
  have hnrd_smul : ∀ (q : ℚ) (y : ℍ[ℚ, a₁, b₁]), nrd (q • y) = q ^ 2 * nrd y := by
    intro q y; rcases y with ⟨y₀, y₁, y₂, y₃⟩; simp [nrd]; ring
  rw [hsm, hsm, hnrd_smul, hnrd_smul, hnrd_smul] at hn

  rcases hγ with hγ | hγ
  · refine ⟨2 * (i + i' + c₀) + i₀, 2 * (j'' + j' + c₀) + 2 * (c + K) + j₀, Or.inl ?_⟩
    have : nrd (z : ℍ[ℚ, a₁, b₁]) * (r : ℚ) ^ (2 * (i + i' + c₀) + i₀) =
        ((((r ^ (i + i' + c₀) : ℕ) : ℤ) : ℚ) ^ 2 * nrd (z : ℍ[ℚ, a₁, b₁])) * (r : ℚ) ^ i₀ := by push_cast; ring
    rw [this, hn]
    have : ((((r ^ (j'' + j' + c₀) : ℕ) : ℤ) : ℚ)) ^ 2 * (((r ^ (c + K) : ℕ) : ℚ) ^ 2 * nrd ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) * (r : ℚ) ^ i₀ =
        ((((r ^ (j'' + j' + c₀) : ℕ) : ℤ) : ℚ)) ^ 2 * ((r ^ (c + K) : ℕ) : ℚ) ^ 2 * (nrd ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (r : ℚ) ^ i₀) := by ring
    rw [this, hγ]; push_cast; ring
  · refine ⟨2 * (i + i' + c₀) + i₀, 2 * (j'' + j' + c₀) + 2 * (c + K) + j₀, Or.inr ?_⟩
    have : nrd (z : ℍ[ℚ, a₁, b₁]) * (r : ℚ) ^ (2 * (i + i' + c₀) + i₀) =
        ((((r ^ (i + i' + c₀) : ℕ) : ℤ) : ℚ) ^ 2 * nrd (z : ℍ[ℚ, a₁, b₁])) * (r : ℚ) ^ i₀ := by push_cast; ring
    rw [this, hn]
    have : ((((r ^ (j'' + j' + c₀) : ℕ) : ℤ) : ℚ)) ^ 2 * (((r ^ (c + K) : ℕ) : ℚ) ^ 2 * nrd ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) * (r : ℚ) ^ i₀ =
        ((((r ^ (j'' + j' + c₀) : ℕ) : ℤ) : ℚ)) ^ 2 * ((r ^ (c + K) : ℕ) : ℚ) ^ 2 * (nrd ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (r : ℚ) ^ i₀) := by ring
    rw [this, hγ]; push_cast; ring

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nrd_mul_pow_eq_of_isIsogenyPair_pow_of_endomorphismDictionary
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nrd_mul_pow_eq_of_isIsogenyPair_pow_of_endomorphismDictionary (solution)
