-- Prove2me | solution 1 for CohCarrier.injective_and_residual_cornerSubmodule_of_isEis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9828e5c9-80d3-57a1-a0e6-e2a8ce0162f3

import Mathlib
import Definitions.Def_CohCarrier_Tower
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_injective_and_residual_of_isEis
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace U3Corner

open CohCarrier Polynomial IharaLemma

section Coeff

variable {𝒪 : Type} [CommRing 𝒪] {A B : Type} [AddCommGroup A] [AddCommGroup B]
  [Module 𝒪 A] [Module 𝒪 B] (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def coefL (g : A →ₗ[𝒪] B) : H1 M H A →ₗ[𝒪] H1 M H B where
  toFun φ := g.toAddMonoidHom.comp φ
  map_add' φ ψ := by ext; simp
  map_smul' r φ := by ext; simp

@[scoped simp] theorem coefL_apply (g : A →ₗ[𝒪] B) (φ : H1 M H A) :
    coefL M H g φ = g.toAddMonoidHom.comp φ := rfl

end Coeff

section Corner

variable {𝒪 : Type} [CommRing 𝒪]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V]
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
variable (Sp : IdempotentSplitting 𝕋) (i₀ : Fin Sp.n)

theorem exists_mul_mul_e_eq {u : 𝕋} (hu : u ∉ Sp.𝔪 i₀) : ∃ t : 𝕋, t * u * Sp.e i₀ = Sp.e i₀ :=
  exists_mul_mul_eq_of_notMem (Sp.idem i₀) (Sp.𝔪 i₀) (Sp.mem_of_isMaximal_of_ne i₀) hu

theorem exists_smul_eq_of_notMem {u : 𝕋} (hu : u ∉ Sp.𝔪 i₀) (m : V)
    (hm : m ∈ cornerSubmodule (M := V) (Sp.e i₀)) :
    ∃ m' : V, m' ∈ cornerSubmodule (M := V) (Sp.e i₀) ∧ u • m' = m := by
  obtain ⟨t, ht⟩ := exists_mul_mul_e_eq Sp i₀ hu
  have hem : Sp.e i₀ • m = m := Sp.e_smul_coe i₀ ⟨m, hm⟩
  refine ⟨t • m, Submodule.smul_mem _ t hm, ?_⟩
  calc u • t • m = u • t • (Sp.e i₀ • m) := by rw [hem]
    _ = (t * u * Sp.e i₀) • m := by rw [smul_smul, smul_smul, mul_comm u t]
    _ = m := by rw [ht, hem]

theorem eq_zero_of_smul_eq_zero_of_notMem {u : 𝕋} (hu : u ∉ Sp.𝔪 i₀) (m : V)
    (hm : m ∈ cornerSubmodule (M := V) (Sp.e i₀)) (h : u • m = 0) : m = 0 := by
  obtain ⟨t, ht⟩ := exists_mul_mul_e_eq Sp i₀ hu
  have hem : Sp.e i₀ • m = m := Sp.e_smul_coe i₀ ⟨m, hm⟩
  calc m = Sp.e i₀ • m := hem.symm
    _ = (t * u * Sp.e i₀) • m := by rw [ht]
    _ = t • u • (Sp.e i₀ • m) := by rw [smul_smul, smul_smul]
    _ = 0 := by rw [hem, h, smul_zero]

theorem eq_zero_of_pow_smul_eq_zero_of_notMem {u : 𝕋} (hu : u ∉ Sp.𝔪 i₀) (n : ℕ) (m : V)
    (hm : m ∈ cornerSubmodule (M := V) (Sp.e i₀)) (h : u ^ n • m = 0) : m = 0 := by
  have hun : u ^ n ∉ Sp.𝔪 i₀ := fun h' => hu ((Sp.isMaximal i₀).isPrime.mem_of_pow_mem n h')
  exact eq_zero_of_smul_eq_zero_of_notMem Sp i₀ hun m hm h

theorem exists_pow_smul_eq_of_notMem {u : 𝕋} (hu : u ∉ Sp.𝔪 i₀) (n : ℕ) (m : V)
    (hm : m ∈ cornerSubmodule (M := V) (Sp.e i₀)) :
    ∃ m' : V, m' ∈ cornerSubmodule (M := V) (Sp.e i₀) ∧ u ^ n • m' = m := by
  have hun : u ^ n ∉ Sp.𝔪 i₀ := fun h' => hu ((Sp.isMaximal i₀).isPrime.mem_of_pow_mem n h')
  exact exists_smul_eq_of_notMem Sp i₀ hun m hm

theorem e_smul_eq_of_mem {v : V} (hv : v ∈ cornerSubmodule (M := V) (Sp.e i₀)) :
    Sp.e i₀ • v = v :=
  Sp.e_smul_coe i₀ ⟨v, hv⟩

theorem smul_mem_corner (t : 𝕋) {v : V} (hv : v ∈ cornerSubmodule (M := V) (Sp.e i₀)) :
    t • v ∈ cornerSubmodule (M := V) (Sp.e i₀) :=
  Submodule.smul_mem _ t hv

theorem e_smul_mem_corner (v : V) : Sp.e i₀ • v ∈ cornerSubmodule (M := V) (Sp.e i₀) :=
  ⟨v, rfl⟩

end Corner

section TwPow

variable {𝒪 : Type} [CommRing 𝒪] (N : ℕ) (ℓ₀ : ℕ) [NeZero ℓ₀]
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 N ⊤ 𝒪)]
  [IsScalarTower 𝒪 𝕋 (H1 N ⊤ 𝒪)]

theorem tw_pow_smul_of (tℓ : 𝕋) (htℓ : ∀ v : H1 N ⊤ 𝒪, tℓ • v = heckeT N ⊤ ℓ₀ 𝒪 v)
    (n : ℕ) (v : H1 N ⊤ 𝒪) :
    (tw 𝒪 ℓ₀) ^ n • Module.AEval'.of (heckeTLin 𝒪 𝒪 N ⊤ ℓ₀) v
      = Module.AEval'.of (heckeTLin 𝒪 𝒪 N ⊤ ℓ₀) ((tℓ - ((ℓ₀ : 𝕋) + 1)) ^ n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, tw_smul_of, pow_succ', mul_smul]
    congr 1
    rw [sub_smul, htℓ, add_smul, one_smul, add_smul, one_smul]
    congr 2
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

end TwPow

section Legs

variable (𝒪 : Type) [CommRing 𝒪] (ℓ₀ : ℕ) [NeZero ℓ₀]

def legI {A : Type} [AddCommGroup A] [Module 𝒪 A] {M M' d : ℕ} [NeZero d]
    (h : LevelLE M M' ⊤ ⊤ d) (hℓ : ℓ₀.Prime) (hcop : Nat.Coprime ℓ₀ d) (hM' : ¬ ℓ₀ ∣ M') :
    Car 𝒪 A M ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 A M' ⊤ ℓ₀ :=
  legOfComm 𝒪 ℓ₀ (iDegL M M' ⊤ ⊤ d A 𝒪 h) (fun φ => iDeg_heckeT_comm_of_coprime h hcop hℓ hM' φ)

theorem legI_of {A : Type} [AddCommGroup A] [Module 𝒪 A] {M M' d : ℕ} [NeZero d]
    (h : LevelLE M M' ⊤ ⊤ d) (hℓ : ℓ₀.Prime) (hcop : Nat.Coprime ℓ₀ d) (hM' : ¬ ℓ₀ ∣ M')
    (φ : H1 M ⊤ A) :
    legI 𝒪 ℓ₀ h hℓ hcop hM' (Module.AEval'.of (heckeTLin 𝒪 A M ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin 𝒪 A M' ⊤ ℓ₀) (iDeg' M M' ⊤ ⊤ d A h φ) :=
  legOfComm_of 𝒪 ℓ₀ _ _ φ

def legC {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module 𝒪 A] [Module 𝒪 B] (M : ℕ)
    (g : A →ₗ[𝒪] B) : Car 𝒪 A M ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 B M ⊤ ℓ₀ :=
  legOfComm 𝒪 ℓ₀ (coefL M ⊤ g) (fun φ => (heckeT_comp_coeff M ⊤ ℓ₀ g.toAddMonoidHom φ).symm)

theorem legC_of {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module 𝒪 A] [Module 𝒪 B]
    (M : ℕ) (g : A →ₗ[𝒪] B) (φ : H1 M ⊤ A) :
    legC 𝒪 ℓ₀ M g (Module.AEval'.of (heckeTLin 𝒪 A M ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin 𝒪 B M ⊤ ℓ₀) (g.toAddMonoidHom.comp φ) :=
  legOfComm_of 𝒪 ℓ₀ _ _ φ

def legT {A : Type} [AddCommGroup A] [Module 𝒪 A] (N q : ℕ) [NeZero q] (hℓ : ℓ₀.Prime)
    (hcop : Nat.Coprime ℓ₀ q) : Car 𝒪 A N ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 A N ⊤ ℓ₀ :=
  legOfComm 𝒪 ℓ₀ (heckeTLin 𝒪 A N ⊤ q) (fun φ => (heckeT_comm_of_prime N ⊤ ℓ₀ q hℓ hcop φ).symm)

theorem legT_of {A : Type} [AddCommGroup A] [Module 𝒪 A] (N q : ℕ) [NeZero q] (hℓ : ℓ₀.Prime)
    (hcop : Nat.Coprime ℓ₀ q) (φ : H1 N ⊤ A) :
    legT 𝒪 ℓ₀ N q hℓ hcop (Module.AEval'.of (heckeTLin 𝒪 A N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin 𝒪 A N ⊤ ℓ₀) (heckeT N ⊤ q A φ) :=
  legOfComm_of 𝒪 ℓ₀ _ _ φ

abbrev loc (A : Type) [AddCommGroup A] [Module 𝒪 A] (M : ℕ) :
    Car 𝒪 A M ⊤ ℓ₀ →ₗ[𝒪[X]] LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 A M ⊤ ℓ₀) :=
  LocalizedModule.mkLinearMap (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 A M ⊤ ℓ₀)

abbrev ofCar (A : Type) [AddCommGroup A] [Module 𝒪 A] (M : ℕ) : H1 M ⊤ A ≃ₗ[𝒪] Car 𝒪 A M ⊤ ℓ₀ :=
  Module.AEval'.of (heckeTLin 𝒪 A M ⊤ ℓ₀)

abbrev locMap {A : Type} [AddCommGroup A] [Module 𝒪 A] {B : Type} [AddCommGroup B] [Module 𝒪 B]
    {M M' : ℕ} (f : Car 𝒪 A M ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 B M' ⊤ ℓ₀) :
    LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 A M ⊤ ℓ₀) →ₗ[𝒪[X]]
      LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 B M' ⊤ ℓ₀) :=
  IsLocalizedModule.map (Submonoid.powers (tw 𝒪 ℓ₀)) (loc 𝒪 ℓ₀ A M) (loc 𝒪 ℓ₀ B M') f

theorem locMap_loc {A : Type} [AddCommGroup A] [Module 𝒪 A] {B : Type} [AddCommGroup B]
    [Module 𝒪 B] {M M' : ℕ} (f : Car 𝒪 A M ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 B M' ⊤ ℓ₀) (v : Car 𝒪 A M ⊤ ℓ₀) :
    locMap 𝒪 ℓ₀ f (loc 𝒪 ℓ₀ A M v) = loc 𝒪 ℓ₀ B M' (f v) :=
  IsLocalizedModule.map_apply _ _ _ f v

def TA3 {A : Type} [AddCommGroup A] [Module 𝒪 A] {N N' N'' : ℕ}
    (rL d : Car 𝒪 A N ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 A N' ⊤ ℓ₀)
    (i j : Car 𝒪 A N' ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 A N'' ⊤ ℓ₀) :
    (LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 A N ⊤ ℓ₀) ×
      LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 A N ⊤ ℓ₀) ×
      LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 A N ⊤ ℓ₀)) →ₗ[𝒪[X]]
      LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 A N'' ⊤ ℓ₀) :=
  locMap 𝒪 ℓ₀ (i ∘ₗ rL) ∘ₗ LinearMap.fst _ _ _ +
    (locMap 𝒪 ℓ₀ (j ∘ₗ rL) ∘ₗ LinearMap.fst _ _ _ +
      locMap 𝒪 ℓ₀ (j ∘ₗ d) ∘ₗ LinearMap.snd _ _ _) ∘ₗ LinearMap.snd _ _ _

theorem TA3_apply {A : Type} [AddCommGroup A] [Module 𝒪 A] {N N' N'' : ℕ}
    (rL d : Car 𝒪 A N ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 A N' ⊤ ℓ₀)
    (i j : Car 𝒪 A N' ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 A N'' ⊤ ℓ₀)
    (f : Car 𝒪 A N ⊤ ℓ₀ × Car 𝒪 A N ⊤ ℓ₀ × Car 𝒪 A N ⊤ ℓ₀) :
    TA3 𝒪 ℓ₀ rL d i j (loc 𝒪 ℓ₀ A N f.1, loc 𝒪 ℓ₀ A N f.2.1, loc 𝒪 ℓ₀ A N f.2.2)
      = loc 𝒪 ℓ₀ A N'' (threeCopy rL d i j f) := by
  rw [threeCopy_apply, map_add, map_add]
  simp only [TA3, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, locMap_loc]

end Legs

section Main

theorem TA3_apply3 (𝒪 : Type) [CommRing 𝒪] (ℓ₀ : ℕ) [NeZero ℓ₀]
    {A : Type} [AddCommGroup A] [Module 𝒪 A] {N N' N'' : ℕ}
    (rL d : Car 𝒪 A N ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 A N' ⊤ ℓ₀)
    (i j : Car 𝒪 A N' ⊤ ℓ₀ →ₗ[𝒪[X]] Car 𝒪 A N'' ⊤ ℓ₀)
    (a b c : Car 𝒪 A N ⊤ ℓ₀) :
    TA3 𝒪 ℓ₀ rL d i j (loc 𝒪 ℓ₀ A N a, loc 𝒪 ℓ₀ A N b, loc 𝒪 ℓ₀ A N c)
      = loc 𝒪 ℓ₀ A N'' (i (rL a) + (j (rL b) + j (d c))) := by
  have h := TA3_apply 𝒪 ℓ₀ rL d i j (a, b, c)
  rw [threeCopy_apply] at h
  exact h

abbrev kk (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] : Type := IsLocalRing.ResidueField 𝒪

abbrev gg (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] : 𝒪 →ₗ[𝒪] kk 𝒪 :=
  Algebra.linearMap 𝒪 (kk 𝒪)

set_option maxHeartbeats 8000000 in

theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (N q : ℕ) [NeZero q] (hqu : IsUnit (q : 𝒪))
    (h₁ : CohCarrier.LevelLE N (N * q) ⊤ ⊤ 1) (hq : CohCarrier.LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : CohCarrier.LevelLE (N * q) (N * q * q) ⊤ ⊤ 1)
    (hq' : CohCarrier.LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (ℓ₀ : ℕ) [NeZero ℓ₀] (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N) (hℓ₀q : ¬ ℓ₀ ∣ q)
    (hihara : ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A],
      (∀ a : A, (q : ℤ) • a = 0 → a = 0) →
      (∀ g h : CohCarrier.H1 N ⊤ A,
          CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + CohCarrier.iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 →
            CohCarrier.IsEis 𝒪 A N ⊤ ℓ₀ g ∧ CohCarrier.IsEis 𝒪 A N ⊤ ℓ₀ h) ∧
      (∀ x z' : CohCarrier.H1 (N * q) ⊤ A,
          CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x +
              CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
            ∃ w : CohCarrier.H1 N ⊤ A,
              CohCarrier.IsEis 𝒪 A (N * q) ⊤ ℓ₀ (z' - CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
                CohCarrier.IsEis 𝒪 A (N * q) ⊤ ℓ₀ (x + CohCarrier.iDeg' N (N * q) ⊤ ⊤ q A hq w)))
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 N ⊤ 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 N ⊤ 𝒪)]
    (Sp : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin Sp.n)
    (tℓ : 𝕋) (htℓ : ∀ v : CohCarrier.H1 N ⊤ 𝒪, tℓ • v = CohCarrier.heckeT N ⊤ ℓ₀ 𝒪 v)
    (hEis : tℓ - ((ℓ₀ : 𝕋) + 1) ∉ Sp.𝔪 i₀) :
    (∀ v : CohCarrier.H1 N ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
        q • CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 𝒪 h₁'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ v)
            - CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ (CohCarrier.heckeT N ⊤ q 𝒪 v))
            + CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ q 𝒪 hq v) = 0 →
        v = 0) ∧
    (∀ v : CohCarrier.H1 N ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
        ∀ x : CohCarrier.H1 (N * q * q) ⊤ 𝒪,
        q • CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 𝒪 h₁'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ v)
            - CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ (CohCarrier.heckeT N ⊤ q 𝒪 v))
            + CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ q 𝒪 hq v) = ϖ • x →
        ∃ v₁ : CohCarrier.H1 N ⊤ 𝒪,
          v₁ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) ∧ v = ϖ • v₁) := by
  classical

  have hcopq : Nat.Coprime ℓ₀ q := (Nat.Prime.coprime_iff_not_dvd hℓ₀).mpr hℓ₀q
  have hcop1 : Nat.Coprime ℓ₀ 1 := Nat.coprime_one_right _
  have hℓNq : ¬ ℓ₀ ∣ N * q := fun h => (hℓ₀.dvd_mul.mp h).elim hℓ₀N hℓ₀q
  have hℓNqq : ¬ ℓ₀ ∣ N * q * q := fun h => (hℓ₀.dvd_mul.mp h).elim hℓNq hℓ₀q
  have hg : ∀ a : 𝒪, gg 𝒪 a = IsLocalRing.residue 𝒪 a := fun a => rfl
  have hker : ∀ a, gg 𝒪 a = 0 → ∃ a₁, a = ϖ • a₁ := by
    intro a ha
    rw [hg, IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
    obtain ⟨a₁, rfl⟩ := ha
    exact ⟨a₁, by rw [smul_eq_mul, mul_comm]⟩
  have hreg : ∀ a : 𝒪, ϖ • a = 0 → a = 0 := fun a ha =>
    (mul_eq_zero.mp ha).resolve_left hϖ.ne_zero
  have hB : ∀ b : kk 𝒪, ϖ • b = 0 := by
    intro b
    rw [Algebra.smul_def, show algebraMap 𝒪 (kk 𝒪) ϖ = IsLocalRing.residue 𝒪 ϖ from rfl,
      (IsLocalRing.residue_eq_zero_iff ϖ).mpr, zero_mul]
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ

  have hq0 : (q : 𝒪) ≠ 0 := hqu.ne_zero
  have hAq : ∀ a : 𝒪, (q : ℤ) • a = 0 → a = 0 := by
    intro a ha
    rw [zsmul_eq_mul, Int.cast_natCast] at ha
    exact (mul_eq_zero.mp ha).resolve_left hq0
  have hkq : ∀ b : kk 𝒪, (q : ℤ) • b = 0 → b = 0 := by
    intro b hb
    rw [zsmul_eq_mul, Int.cast_natCast] at hb
    have hqk : (q : kk 𝒪) ≠ 0 := by
      rw [show (q : kk 𝒪) = algebraMap 𝒪 (kk 𝒪) (q : 𝒪) by simp]
      exact (hqu.map (algebraMap 𝒪 (kk 𝒪))).ne_zero
    exact (mul_eq_zero.mp hb).resolve_left hqk
  obtain ⟨hcoreA, h25A⟩ := hihara 𝒪 hAq
  obtain ⟨hcoreB, h25B⟩ := hihara (kk 𝒪) hkq

  obtain ⟨hinj, hres⟩ := CohCarrier.injective_and_residual_of_isEis
    (VA := LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 𝒪 N ⊤ ℓ₀))
    (LA := LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 𝒪 (N * q * q) ⊤ ℓ₀))
    (VB := LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 (kk 𝒪) N ⊤ ℓ₀))
    (LB := LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 (kk 𝒪) (N * q * q) ⊤ ℓ₀))
    𝒪 𝒪 ℓ₀ N q h₁ hq h₁' hq'
    (kk 𝒪) ϖ (gg 𝒪) hker hreg hB
    (legI 𝒪 ℓ₀ h₁ hℓ₀ hcop1 hℓNq) (legI 𝒪 ℓ₀ hq hℓ₀ hcopq hℓNq)
    (legI 𝒪 ℓ₀ h₁' hℓ₀ hcop1 hℓNqq) (legI 𝒪 ℓ₀ hq' hℓ₀ hcopq hℓNqq)
    (fun φ => legI_of 𝒪 ℓ₀ h₁ hℓ₀ hcop1 hℓNq φ) (fun φ => legI_of 𝒪 ℓ₀ hq hℓ₀ hcopq hℓNq φ)
    (fun ψ => legI_of 𝒪 ℓ₀ h₁' hℓ₀ hcop1 hℓNqq ψ) (fun ψ => legI_of 𝒪 ℓ₀ hq' hℓ₀ hcopq hℓNqq ψ)
    (legI 𝒪 ℓ₀ (A := kk 𝒪) h₁ hℓ₀ hcop1 hℓNq) (legI 𝒪 ℓ₀ (A := kk 𝒪) hq hℓ₀ hcopq hℓNq)
    (legI 𝒪 ℓ₀ (A := kk 𝒪) h₁' hℓ₀ hcop1 hℓNqq) (legI 𝒪 ℓ₀ (A := kk 𝒪) hq' hℓ₀ hcopq hℓNqq)
    (fun φ => legI_of 𝒪 ℓ₀ h₁ hℓ₀ hcop1 hℓNq φ) (fun φ => legI_of 𝒪 ℓ₀ hq hℓ₀ hcopq hℓNq φ)
    (fun ψ => legI_of 𝒪 ℓ₀ h₁' hℓ₀ hcop1 hℓNqq ψ) (fun ψ => legI_of 𝒪 ℓ₀ hq' hℓ₀ hcopq hℓNqq ψ)
    (legC 𝒪 ℓ₀ N (gg 𝒪)) (fun φ => legC_of 𝒪 ℓ₀ N (gg 𝒪) φ)
    (legC 𝒪 ℓ₀ (N * q * q) (gg 𝒪)) (fun ψ => legC_of 𝒪 ℓ₀ (N * q * q) (gg 𝒪) ψ)
    (loc 𝒪 ℓ₀ 𝒪 N) (loc 𝒪 ℓ₀ 𝒪 (N * q * q)) (loc 𝒪 ℓ₀ (kk 𝒪) N) (loc 𝒪 ℓ₀ (kk 𝒪) (N * q * q))
    hcoreA h25A hcoreB h25B
    (TA3 𝒪 ℓ₀ (legI 𝒪 ℓ₀ h₁ hℓ₀ hcop1 hℓNq) (legI 𝒪 ℓ₀ hq hℓ₀ hcopq hℓNq)
      (legI 𝒪 ℓ₀ h₁' hℓ₀ hcop1 hℓNqq) (legI 𝒪 ℓ₀ hq' hℓ₀ hcopq hℓNqq))
    (fun f => TA3_apply 𝒪 ℓ₀ _ _ _ _ f)
    (TA3 𝒪 ℓ₀ (legI 𝒪 ℓ₀ (A := kk 𝒪) h₁ hℓ₀ hcop1 hℓNq) (legI 𝒪 ℓ₀ (A := kk 𝒪) hq hℓ₀ hcopq hℓNq)
      (legI 𝒪 ℓ₀ (A := kk 𝒪) h₁' hℓ₀ hcop1 hℓNqq) (legI 𝒪 ℓ₀ (A := kk 𝒪) hq' hℓ₀ hcopq hℓNqq))
    (fun f => TA3_apply 𝒪 ℓ₀ _ _ _ _ f)
    (locMap 𝒪 ℓ₀ (legC 𝒪 ℓ₀ N (gg 𝒪))) (fun v => locMap_loc 𝒪 ℓ₀ _ v)
    (locMap 𝒪 ℓ₀ (legC 𝒪 ℓ₀ (N * q * q) (gg 𝒪))) (fun x => locMap_loc 𝒪 ℓ₀ _ x)
    (locMap 𝒪 ℓ₀ (legT 𝒪 ℓ₀ N q hℓ₀ hcopq))

  set S : Submonoid 𝒪[X] := Submonoid.powers (tw 𝒪 ℓ₀) with hS
  set W := TA3 𝒪 ℓ₀ (legI 𝒪 ℓ₀ h₁ hℓ₀ hcop1 hℓNq) (legI 𝒪 ℓ₀ hq hℓ₀ hcopq hℓNq)
      (legI 𝒪 ℓ₀ h₁' hℓ₀ hcop1 hℓNqq) (legI 𝒪 ℓ₀ hq' hℓ₀ hcopq hℓNqq) ∘ₗ
    embComb (V := LocalizedModule (Submonoid.powers (tw 𝒪 ℓ₀)) (Car 𝒪 𝒪 N ⊤ ℓ₀))
      (q : 𝒪[X]) (locMap 𝒪 ℓ₀ (legT 𝒪 ℓ₀ N q hℓ₀ hcopq)) with hW
  set u : 𝕋 := tℓ - ((ℓ₀ : 𝕋) + 1) with hu

  have hWof : ∀ v : H1 N ⊤ 𝒪, W (loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N v)) =
      loc 𝒪 ℓ₀ 𝒪 (N * q * q) (ofCar 𝒪 ℓ₀ 𝒪 (N * q * q)
      (q • iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 𝒪 h₁' (iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ v)
        - iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq' (iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ (heckeT N ⊤ q 𝒪 v))
        + iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq' (iDeg' N (N * q) ⊤ ⊤ q 𝒪 hq v))) := by
    intro v
    rw [hW, LinearMap.comp_apply, embComb_apply]
    have e1 : (q : 𝒪[X]) • loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N v)
        = loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N (q • v)) := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← map_nsmul]
    have e2 : -(locMap 𝒪 ℓ₀ (legT 𝒪 ℓ₀ N q hℓ₀ hcopq)) (loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N v))
        = loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N (-(heckeT N ⊤ q 𝒪 v))) := by
      rw [locMap_loc, legT_of, map_neg, map_neg]
    rw [e1, e2, TA3_apply3, legI_of, legI_of, legI_of, legI_of, legI_of, legI_of,
      ← LinearEquiv.map_add, ← LinearEquiv.map_add]
    congr 2
    simp only [map_nsmul, map_neg]
    abel

  refine ⟨?_, ?_⟩
  · intro v hv h0
    have hz1 : ofCar 𝒪 ℓ₀ 𝒪 (N * q * q) 0 = 0 := LinearEquiv.map_zero _
    have hz2 : loc 𝒪 ℓ₀ 𝒪 (N * q * q) 0 = 0 := LinearMap.map_zero _
    have hW0 : W (loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N v)) = 0 := by rw [hWof, h0, hz1, hz2]
    have hW00 : W (loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N v)) = W 0 :=
      hW0.trans (LinearMap.map_zero W).symm
    have hg0 : loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N v) = 0 := hinj hW00
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S (loc 𝒪 ℓ₀ 𝒪 N)).mp hg0
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    change ((s : 𝒪[X])) • ofCar 𝒪 ℓ₀ 𝒪 N v = 0 at hs
    rw [← hn, tw_pow_smul_of N ℓ₀ tℓ htℓ n v, LinearEquiv.map_eq_zero_iff] at hs
    exact eq_zero_of_pow_smul_eq_zero_of_notMem Sp i₀ hEis n v hv hs

  · intro v hv x hx
    have hs1 : ofCar 𝒪 ℓ₀ 𝒪 (N * q * q) (ϖ • x) = ϖ • ofCar 𝒪 ℓ₀ 𝒪 (N * q * q) x :=
      map_smul _ ϖ x
    have hs2 : ϖ • ofCar 𝒪 ℓ₀ 𝒪 (N * q * q) x = (C ϖ : 𝒪[X]) • ofCar 𝒪 ℓ₀ 𝒪 (N * q * q) x :=
      (Module.AEval.C_smul _ ϖ _).symm
    have hs3 : loc 𝒪 ℓ₀ 𝒪 (N * q * q) ((C ϖ : 𝒪[X]) • ofCar 𝒪 ℓ₀ 𝒪 (N * q * q) x)
        = (C ϖ : 𝒪[X]) • loc 𝒪 ℓ₀ 𝒪 (N * q * q) (ofCar 𝒪 ℓ₀ 𝒪 (N * q * q) x) :=
      map_smul _ _ _
    have hWx : W (loc 𝒪 ℓ₀ 𝒪 N (ofCar 𝒪 ℓ₀ 𝒪 N v))
        = (C ϖ : 𝒪[X]) • loc 𝒪 ℓ₀ 𝒪 (N * q * q) (ofCar 𝒪 ℓ₀ 𝒪 (N * q * q) x) := by
      rw [hWof, hx, hs1, hs2, hs3]
    obtain ⟨y, hy⟩ := hres _ _ hWx
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
      rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨c, hc⟩ := hy
      obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
      set m₀ : H1 N ⊤ 𝒪 := (ofCar 𝒪 ℓ₀ 𝒪 N).symm m with hm₀
      have hm : m = ofCar 𝒪 ℓ₀ 𝒪 N m₀ := (LinearEquiv.apply_symm_apply _ _).symm
      have hs4 : (C ϖ : 𝒪[X]) • ofCar 𝒪 ℓ₀ 𝒪 N m₀ = ofCar 𝒪 ℓ₀ 𝒪 N (ϖ • m₀) :=
        (Module.AEval.C_smul _ ϖ _).trans (map_smul _ ϖ m₀).symm
      change (c : 𝒪[X]) • ((s : 𝒪[X]) • ofCar 𝒪 ℓ₀ 𝒪 N v)
        = (c : 𝒪[X]) • ((1 : 𝒪[X]) • ((C ϖ : 𝒪[X]) • m)) at hc
      rw [one_smul, ← ha, ← hb, hm, hs4, tw_pow_smul_of N ℓ₀ tℓ htℓ b,
        tw_pow_smul_of N ℓ₀ tℓ htℓ a, tw_pow_smul_of N ℓ₀ tℓ htℓ a] at hc
      have hc' : u ^ a • u ^ b • v = u ^ a • ϖ • m₀ := (ofCar 𝒪 ℓ₀ 𝒪 N).injective hc

      have hcorner : u ^ a • (u ^ b • v - ϖ • (Sp.e i₀ • m₀)) = 0 := by
        have h2 : Sp.e i₀ • (u ^ a • u ^ b • v) = Sp.e i₀ • (u ^ a • ϖ • m₀) := by rw [hc']
        rw [smul_comm (Sp.e i₀) (u ^ a), smul_comm (Sp.e i₀) (u ^ b),
          e_smul_eq_of_mem Sp i₀ hv, smul_comm (Sp.e i₀) (u ^ a),
          smul_comm (Sp.e i₀) ϖ] at h2
        rw [smul_sub, sub_eq_zero]
        exact h2
      have hmem : u ^ b • v - ϖ • (Sp.e i₀ • m₀) ∈ cornerSubmodule (M := H1 N ⊤ 𝒪) (Sp.e i₀) :=
        Submodule.sub_mem _ (smul_mem_corner Sp i₀ _ hv)
          (Submodule.smul_of_tower_mem _ ϖ (e_smul_mem_corner Sp i₀ m₀))
      have hzero := eq_zero_of_pow_smul_eq_zero_of_notMem Sp i₀ hEis a _ hmem hcorner
      rw [sub_eq_zero] at hzero

      obtain ⟨m₂, hm₂, hm₂eq⟩ := exists_pow_smul_eq_of_notMem Sp i₀ hEis b (Sp.e i₀ • m₀)
        (e_smul_mem_corner Sp i₀ m₀)
      refine ⟨m₂, hm₂, ?_⟩
      have hdiff : u ^ b • (v - ϖ • m₂) = 0 := by
        rw [smul_sub, hzero, ← hm₂eq, smul_comm ϖ (u ^ b) m₂, sub_self]
      have hmem2 : v - ϖ • m₂ ∈ cornerSubmodule (M := H1 N ⊤ 𝒪) (Sp.e i₀) :=
        Submodule.sub_mem _ hv (Submodule.smul_of_tower_mem _ ϖ hm₂)
      have := eq_zero_of_pow_smul_eq_zero_of_notMem Sp i₀ hEis b _ hmem2 hdiff
      rwa [sub_eq_zero] at this

end Main

end U3Corner
p2m_reactivate "P2MW.S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis.U3Corner"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (N q : ℕ) [NeZero q] (hqu : IsUnit (q : 𝒪))
    (h₁ : CohCarrier.LevelLE N (N * q) ⊤ ⊤ 1) (hq : CohCarrier.LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : CohCarrier.LevelLE (N * q) (N * q * q) ⊤ ⊤ 1)
    (hq' : CohCarrier.LevelLE (N * q) (N * q * q) ⊤ ⊤ q)

    (ℓ₀ : ℕ) [NeZero ℓ₀] (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N) (hℓ₀q : ¬ ℓ₀ ∣ q)

    (hihara : ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A],
      (∀ a : A, (q : ℤ) • a = 0 → a = 0) →
      (∀ g h : CohCarrier.H1 N ⊤ A,
          CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + CohCarrier.iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 →
            CohCarrier.IsEis 𝒪 A N ⊤ ℓ₀ g ∧ CohCarrier.IsEis 𝒪 A N ⊤ ℓ₀ h) ∧
      (∀ x z' : CohCarrier.H1 (N * q) ⊤ A,
          CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x +
              CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
            ∃ w : CohCarrier.H1 N ⊤ A,
              CohCarrier.IsEis 𝒪 A (N * q) ⊤ ℓ₀ (z' - CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
                CohCarrier.IsEis 𝒪 A (N * q) ⊤ ℓ₀ (x + CohCarrier.iDeg' N (N * q) ⊤ ⊤ q A hq w)))

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 N ⊤ 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 N ⊤ 𝒪)]
    (Sp : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin Sp.n)
    (tℓ : 𝕋) (htℓ : ∀ v : CohCarrier.H1 N ⊤ 𝒪, tℓ • v = CohCarrier.heckeT N ⊤ ℓ₀ 𝒪 v)
    (hEis : tℓ - ((ℓ₀ : 𝕋) + 1) ∉ Sp.𝔪 i₀) :
    (∀ v : CohCarrier.H1 N ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
        q • CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 𝒪 h₁'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ v)
            - CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ (CohCarrier.heckeT N ⊤ q 𝒪 v))
            + CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ q 𝒪 hq v) = 0 →
        v = 0) ∧
    (∀ v : CohCarrier.H1 N ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) →
        ∀ x : CohCarrier.H1 (N * q * q) ⊤ 𝒪,
        q • CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 𝒪 h₁'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ v)
            - CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ 1 𝒪 h₁ (CohCarrier.heckeT N ⊤ q 𝒪 v))
            + CohCarrier.iDeg' (N * q) (N * q * q) ⊤ ⊤ q 𝒪 hq'
              (CohCarrier.iDeg' N (N * q) ⊤ ⊤ q 𝒪 hq v) = ϖ • x →
        ∃ v₁ : CohCarrier.H1 N ⊤ 𝒪,
          v₁ ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀) ∧ v = ϖ • v₁) :=
  U3Corner.main hϖ N q hqu h₁ hq h₁' hq' ℓ₀ hℓ₀ hℓ₀N hℓ₀q hihara Sp i₀ tℓ htℓ hEis

end
p2m_reactivate "P2MW.S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis.U3Corner"

end S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis
end P2MW
export P2MW.S_CohCarrier_injective_and_residual_cornerSubmodule_of_isEis (solution)
