-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_surjective_algHom_apply_pi_T_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d250db42-5e3f-581a-a4f3-90af12062c10

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_heckeAlgebra_ringHom_ext_of_primeFactors_subset
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_surjective_algHom_apply_pi_T_eq_of_dvd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped MatrixGroups ModularForm

namespace PsiAnemic

open CongruenceSubgroup

theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  rw [ModularForm.val_heckeDiagMatrix one_ne_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {M M' : ℕ} [NeZero M] [NeZero M']

noncomputable def ι (hMM' : M ∣ M') : CuspForm (Gamma0 M) 2 →ₗ[ℂ] CuspForm (Gamma0 M') 2 :=
  FreyPackage.ModMCarrier.rescaleLin (d := 1) (R := M) (M := M') (by simpa using hMM') 2

theorem coe_ι (hMM' : M ∣ M') (f : CuspForm (Gamma0 M) 2) : ⇑(ι hMM' f) = ⇑f := by
  rw [ι, FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one, SlashAction.slash_one]

theorem ι_injective (hMM' : M ∣ M') : Function.Injective (ι hMM') := by
  intro f g h
  have h' : ⇑(ι hMM' f) = ⇑(ι hMM' g) := by rw [h]
  rw [coe_ι hMM' f, coe_ι hMM' g] at h'
  exact DFunLike.coe_injective h'

theorem heckeTLin_ι (hMM' : M ∣ M') {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M')
    (f : CuspForm (Gamma0 M) 2) :
    CuspForm.heckeTLin 2 hℓ hℓM' (ι hMM' f) =
      ι hMM' (CuspForm.heckeTLin 2 hℓ (fun h => hℓM' (h.trans hMM')) f) :=
  CuspForm.heckeTLin_rescaleLin (d := 1) (R := M) (M := M') (by simpa using hMM') hℓ hℓM' _ f

variable {S : Set ℕ}

theorem exists_restrict (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (t : CuspForm.heckeAlgebra M' 2 S) :
    ∃ t₀ : CuspForm.heckeAlgebra M 2 S, ∀ f : CuspForm (Gamma0 M) 2,
      (t : Module.End ℂ (CuspForm (Gamma0 M') 2)) (ι hMM' f) = ι hMM' ((t₀ : Module.End ℂ _) f) := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨ℓ, hℓ, hℓM', hℓS, rfl⟩ | ⟨q, hqM', hq, hqS, rfl⟩
    · exact ⟨CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS,
        fun f => heckeTLin_ι hMM' hℓ hℓM' f⟩
    · exact absurd (hS q hq hqM') hqS
  | algebraMap n =>
    refine ⟨algebraMap ℤ _ n, fun f => ?_⟩
    simp only [Subalgebra.coe_algebraMap, Module.algebraMap_end_apply, map_zsmul]
  | add x y hx hy ihx ihy =>
    obtain ⟨x₀, hx₀⟩ := ihx
    obtain ⟨y₀, hy₀⟩ := ihy
    exact ⟨x₀ + y₀, fun f => by simp only [Subalgebra.coe_add, LinearMap.add_apply, hx₀, hy₀, map_add]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨x₀, hx₀⟩ := ihx
    obtain ⟨y₀, hy₀⟩ := ihy
    exact ⟨x₀ * y₀, fun f => by simp only [Subalgebra.coe_mul, Module.End.mul_apply, hy₀, hx₀]⟩

theorem restrict_unique (hMM' : M ∣ M') (t : CuspForm.heckeAlgebra M' 2 S)
    (t₀ t₁ : CuspForm.heckeAlgebra M 2 S)
    (h₀ : ∀ f, (t : Module.End ℂ (CuspForm (Gamma0 M') 2)) (ι hMM' f) = ι hMM' ((t₀ : Module.End ℂ _) f))
    (h₁ : ∀ f, (t : Module.End ℂ (CuspForm (Gamma0 M') 2)) (ι hMM' f) = ι hMM' ((t₁ : Module.End ℂ _) f)) :
    t₀ = t₁ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  exact ι_injective hMM' ((h₀ f).symm.trans (h₁ f))

noncomputable def φ (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S) :
    CuspForm.heckeAlgebra M' 2 S →+* CuspForm.heckeAlgebra M 2 S where
  toFun t := (exists_restrict hMM' hS t).choose
  map_one' := by
    refine restrict_unique hMM' 1 _ _ (exists_restrict hMM' hS 1).choose_spec (fun f => ?_)
    simp
  map_mul' x y := by
    refine restrict_unique hMM' (x * y) _ _ (exists_restrict hMM' hS (x * y)).choose_spec (fun f => ?_)
    simp only [Subalgebra.coe_mul, Module.End.mul_apply]
    rw [(exists_restrict hMM' hS y).choose_spec f, (exists_restrict hMM' hS x).choose_spec]
  map_zero' := by
    refine restrict_unique hMM' 0 _ _ (exists_restrict hMM' hS 0).choose_spec (fun f => ?_)
    simp
  map_add' x y := by
    refine restrict_unique hMM' (x + y) _ _ (exists_restrict hMM' hS (x + y)).choose_spec (fun f => ?_)
    simp only [Subalgebra.coe_add, LinearMap.add_apply, map_add]
    rw [(exists_restrict hMM' hS y).choose_spec f, (exists_restrict hMM' hS x).choose_spec f]

theorem φ_spec (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (t : CuspForm.heckeAlgebra M' 2 S) (f : CuspForm (Gamma0 M) 2) :
    (t : Module.End ℂ (CuspForm (Gamma0 M') 2)) (ι hMM' f) = ι hMM' ((φ hMM' hS t : Module.End ℂ _) f) :=
  (exists_restrict hMM' hS t).choose_spec f

theorem φ_T (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S) :
    φ hMM' hS (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS) =
      CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS :=
  restrict_unique hMM' _ _ _ (φ_spec hMM' hS _) (fun f => heckeTLin_ι hMM' hℓ hℓM' f)

theorem φ_surjective (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S) :
    Function.Surjective (φ hMM' hS) := by
  intro t₀
  obtain ⟨t₀, ht₀⟩ := t₀
  induction ht₀ using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨ℓ, hℓ, hℓM, hℓS, rfl⟩ | ⟨q, hqM, hq, hqS, rfl⟩
    · have hℓM' : ¬ ℓ ∣ M' := fun h => hℓS (hS ℓ hℓ h)
      exact ⟨CuspForm.heckeAlgebra.T hℓ hℓM' hℓS, φ_T hMM' hS hℓ hℓM' hℓS⟩
    · exact absurd (hS q hq (hqM.trans hMM')) hqS
  | algebraMap n =>
    refine ⟨algebraMap ℤ _ n, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]
    apply Subtype.ext
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, by rw [(φ hMM' hS).map_add, ha, hb]; rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a * b, by rw [(φ hMM' hS).map_mul, ha, hb]; rfl⟩

end PsiAnemic

namespace PsiAnemic

open CongruenceSubgroup
open scoped TensorProduct

variable {M M' : ℕ} [NeZero M] [NeZero M'] {S : Set ℕ}

theorem theta'_eq (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    {R : Type} [CommRing R] (θ : CuspForm.heckeAlgebra M 2 S →+* R) (θ' : CuspForm.heckeAlgebra M' 2 S →+* R)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S),
      θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS) =
        θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS)) :
    θ' = θ.comp (φ hMM' hS) :=
  CuspForm.heckeAlgebra_ringHom_ext_of_primeFactors_subset hS θ' (θ.comp (φ hMM' hS))
    (fun ℓ hℓ hℓN hℓS => by rw [RingHom.comp_apply, φ_T]; exact hθ ℓ hℓ hℓN hℓS)

section Lattice
variable [Fact (CuspForm.HasIntegralStructure M' 2)]

noncomputable def eL' : CuspForm.heckeAlgebra M' 2 S ≃+* CuspForm.heckeLatticeAlgebra M' S :=
  RingEquiv.ofBijective (CuspForm.latticeRestrictHom M' S) (CuspForm.latticeRestrictHom_bijective M' S Fact.out)

theorem eL'_apply (t : CuspForm.heckeAlgebra M' 2 S) :
    (eL' t : CuspForm.heckeLatticeAlgebra M' S) = CuspForm.latticeRestrictHom M' S t := rfl

noncomputable def φL (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S) :
    CuspForm.heckeLatticeAlgebra M' S →+* CuspForm.heckeLatticeAlgebra M S :=
  ((CuspForm.latticeRestrictHom M S).toRingHom.comp (φ hMM' hS)).comp
    (eL' (M' := M') (S := S)).symm.toRingHom

theorem φL_latticeRestrictHom (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (t : CuspForm.heckeAlgebra M' 2 S) :
    φL hMM' hS (CuspForm.latticeRestrictHom M' S t) = CuspForm.latticeRestrictHom M S (φ hMM' hS t) := by
  show ((CuspForm.latticeRestrictHom M S).toRingHom.comp (φ hMM' hS)) (eL'.symm (eL' t)) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem φL_surjective (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S) :
    Function.Surjective (φL hMM' hS) :=
  ((CuspForm.latticeRestrictHom_surjective M S).comp (φ_surjective hMM' hS)).comp
    (eL' (M' := M') (S := S)).symm.surjective

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]

noncomputable def Φ (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S) :
    CuspForm.heckeBaseAlgebra M' S 𝒪 →ₐ[𝒪] CuspForm.heckeBaseAlgebra M S 𝒪 :=
  Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪) (φL hMM' hS).toIntAlgHom

theorem Φ_tmul (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (a : 𝒪) (u : CuspForm.heckeLatticeAlgebra M' S) :
    Φ 𝒪 hMM' hS (a ⊗ₜ[ℤ] u : 𝒪 ⊗[ℤ] ↥(CuspForm.heckeLatticeAlgebra M' S)) =
      (a ⊗ₜ[ℤ] φL hMM' hS u : 𝒪 ⊗[ℤ] ↥(CuspForm.heckeLatticeAlgebra M S)) := rfl

theorem Φ_latticeBaseChange (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (x : 𝒪 ⊗[ℤ] ↥(CuspForm.heckeAlgebra M' 2 S)) :
    Φ 𝒪 hMM' hS (CuspForm.latticeBaseChange M' S 𝒪 x) =
      CuspForm.latticeBaseChange M S 𝒪
        (Algebra.TensorProduct.map (AlgHom.id ℤ 𝒪) (φ hMM' hS).toIntAlgHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a t =>
    rw [CuspForm.latticeBaseChange_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      RingHom.toIntAlgHom_apply, CuspForm.latticeBaseChange_tmul]
    show (a ⊗ₜ[ℤ] φL hMM' hS (CuspForm.latticeRestrictHom M' S t) : 𝒪 ⊗[ℤ] ↥(CuspForm.heckeLatticeAlgebra M S)) = _
    rw [φL_latticeRestrictHom]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Φ_surjective (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S) :
    Function.Surjective (Φ 𝒪 hMM' hS) :=
  Algebra.TensorProduct.map_surjective _ _ Function.surjective_id (φL_surjective hMM' hS)

variable (θ : CuspForm.heckeAlgebra M 2 S →+* IsLocalRing.ResidueField 𝒪)
  (θ' : CuspForm.heckeAlgebra M' 2 S →+* IsLocalRing.ResidueField 𝒪)

theorem residualCharacter_map (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) (x : 𝒪 ⊗[ℤ] ↥(CuspForm.heckeAlgebra M' 2 S)) :
    CuspForm.residualCharacter M S 𝒪 θ (Algebra.TensorProduct.map (AlgHom.id ℤ 𝒪) (φ hMM' hS).toIntAlgHom x) =
      CuspForm.residualCharacter M' S 𝒪 θ' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a t =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, RingHom.toIntAlgHom_apply,
      CuspForm.residualCharacter_tmul, CuspForm.residualCharacter_tmul, hθθ', RingHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem submonoid_le (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) :
    CuspForm.heckeLocalSubmonoid M' S 𝒪 θ' ≤ (CuspForm.heckeLocalSubmonoid M S 𝒪 θ).comap (Φ 𝒪 hMM' hS) := by
  rintro s ⟨x, hx, rfl⟩
  refine ⟨Algebra.TensorProduct.map (AlgHom.id ℤ 𝒪) (φ hMM' hS).toIntAlgHom x, ?_, ?_⟩
  · rw [SetLike.mem_coe, Ideal.mem_primeCompl_iff, CuspForm.mem_heckeCharKernel_iff, residualCharacter_map 𝒪 θ θ' hMM' hS hθθ']
    exact (CuspForm.mem_heckeCharKernel_iff M' S 𝒪 θ' x).not.mp (Ideal.mem_primeCompl_iff.mp hx)
  · exact (Φ_latticeBaseChange 𝒪 hMM' hS x).symm

theorem submonoid_surj (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) (s : CuspForm.heckeBaseAlgebra M S 𝒪)
    (hs : s ∈ CuspForm.heckeLocalSubmonoid M S 𝒪 θ) :
    ∃ s' ∈ CuspForm.heckeLocalSubmonoid M' S 𝒪 θ', Φ 𝒪 hMM' hS s' = s := by
  obtain ⟨y, hy, rfl⟩ := hs
  obtain ⟨x, rfl⟩ := Algebra.TensorProduct.map_surjective (AlgHom.id ℤ 𝒪) (φ hMM' hS).toIntAlgHom
    Function.surjective_id (φ_surjective hMM' hS) y
  refine ⟨CuspForm.latticeBaseChange M' S 𝒪 x, ⟨x, ?_, rfl⟩, Φ_latticeBaseChange 𝒪 hMM' hS x⟩
  rw [SetLike.mem_coe, Ideal.mem_primeCompl_iff, CuspForm.mem_heckeCharKernel_iff, ← residualCharacter_map 𝒪 θ θ' hMM' hS hθθ']
  exact (CuspForm.mem_heckeCharKernel_iff M S 𝒪 θ _).not.mp (Ideal.mem_primeCompl_iff.mp hy)

noncomputable def Ψ₀ (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) :
    CuspForm.heckeLocal M' S 𝒪 θ' →+* CuspForm.heckeLocal M S 𝒪 θ :=
  IsLocalization.map (M := CuspForm.heckeLocalSubmonoid M' S 𝒪 θ') (T := CuspForm.heckeLocalSubmonoid M S 𝒪 θ)
    (CuspForm.heckeLocal M S 𝒪 θ) (Φ 𝒪 hMM' hS).toRingHom (submonoid_le 𝒪 θ θ' hMM' hS hθθ')

theorem Ψ₀_algebraMap (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) (b : CuspForm.heckeBaseAlgebra M' S 𝒪) :
    Ψ₀ 𝒪 θ θ' hMM' hS hθθ' (algebraMap _ (CuspForm.heckeLocal M' S 𝒪 θ') b) =
      algebraMap _ (CuspForm.heckeLocal M S 𝒪 θ) (Φ 𝒪 hMM' hS b) :=
  IsLocalization.map_eq _ b

noncomputable def Ψ (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) :
    CuspForm.heckeLocal M' S 𝒪 θ' →ₐ[𝒪] CuspForm.heckeLocal M S 𝒪 θ :=
  { Ψ₀ 𝒪 θ θ' hMM' hS hθθ' with
    commutes' := fun r => by
      show Ψ₀ 𝒪 θ θ' hMM' hS hθθ' (algebraMap 𝒪 _ r) = algebraMap 𝒪 _ r
      rw [IsScalarTower.algebraMap_apply 𝒪 (CuspForm.heckeBaseAlgebra M' S 𝒪) (CuspForm.heckeLocal M' S 𝒪 θ'),
        Ψ₀_algebraMap, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply 𝒪 (CuspForm.heckeBaseAlgebra M S 𝒪) (CuspForm.heckeLocal M S 𝒪 θ)] }

theorem Ψ_apply (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) (z : CuspForm.heckeLocal M' S 𝒪 θ') :
    Ψ 𝒪 θ θ' hMM' hS hθθ' z = Ψ₀ 𝒪 θ θ' hMM' hS hθθ' z := rfl

theorem Ψ_surjective (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) : Function.Surjective (Ψ 𝒪 θ θ' hMM' hS hθθ') := by
  intro z
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (CuspForm.heckeLocalSubmonoid M S 𝒪 θ) z
  obtain ⟨a', rfl⟩ := Φ_surjective 𝒪 hMM' hS a
  obtain ⟨s', hs', hs'eq⟩ := submonoid_surj 𝒪 θ θ' hMM' hS hθθ' s.1 s.2
  refine ⟨IsLocalization.mk' (CuspForm.heckeLocal M' S 𝒪 θ') a' ⟨s', hs'⟩, ?_⟩
  rw [Ψ_apply, Ψ₀, IsLocalization.map_mk']
  congr 1
  exact Subtype.ext hs'eq

theorem Ψ_π (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) (t : CuspForm.heckeAlgebra M' 2 S) :
    Ψ 𝒪 θ θ' hMM' hS hθθ' (CuspForm.heckeLocal.π M' S 𝒪 θ' t) =
      CuspForm.heckeLocal.π M S 𝒪 θ (φ hMM' hS t) := by
  show Ψ₀ 𝒪 θ θ' hMM' hS hθθ' (algebraMap _ _ (CuspForm.latticeBaseChange M' S 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] t))) =
    algebraMap _ _ (CuspForm.latticeBaseChange M S 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] φ hMM' hS t))
  rw [Ψ₀_algebraMap, Φ_latticeBaseChange, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    RingHom.toIntAlgHom_apply]

theorem Ψ_π_T (hMM' : M ∣ M') (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (hθθ' : θ' = θ.comp (φ hMM' hS)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S) :
    Ψ 𝒪 θ θ' hMM' hS hθθ' (CuspForm.heckeLocal.π M' S 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS)) =
      CuspForm.heckeLocal.π M S 𝒪 θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS) := by
  rw [Ψ_π, φ_T]

theorem ext_π_T (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    {A : Type} [CommRing A] [Algebra 𝒪 A]
    (g g' : CuspForm.heckeLocal M' S 𝒪 θ' →ₐ[𝒪] A)
    (h : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S),
      g (CuspForm.heckeLocal.π M' S 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS)) =
        g' (CuspForm.heckeLocal.π M' S 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS))) :
    g = g' := by

  have hπ : g.toRingHom.comp (CuspForm.heckeLocal.π M' S 𝒪 θ') = g'.toRingHom.comp (CuspForm.heckeLocal.π M' S 𝒪 θ') :=
    CuspForm.heckeAlgebra_ringHom_ext_of_primeFactors_subset hS _ _ (fun ℓ hℓ hℓN hℓS => h ℓ hℓ hℓN hℓS)

  have hbase : g.toRingHom.comp (algebraMap (CuspForm.heckeBaseAlgebra M' S 𝒪) (CuspForm.heckeLocal M' S 𝒪 θ')) =
      g'.toRingHom.comp (algebraMap (CuspForm.heckeBaseAlgebra M' S 𝒪) (CuspForm.heckeLocal M' S 𝒪 θ')) := by
    apply RingHom.coe_addMonoidHom_injective
    apply AddMonoidHom.toIntLinearMap_injective
    apply TensorProduct.ext'
    intro a u
    obtain ⟨t, rfl⟩ := CuspForm.latticeRestrictHom_surjective M' S u
    have hsplit : ((a ⊗ₜ[ℤ] CuspForm.latticeRestrictHom M' S t) : CuspForm.heckeBaseAlgebra M' S 𝒪) =
        algebraMap 𝒪 (CuspForm.heckeBaseAlgebra M' S 𝒪) a * CuspForm.latticeBaseChange M' S 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] t) := by
      rw [← CuspForm.latticeBaseChange_algebraMap, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        CuspForm.latticeBaseChange_tmul]
    change g (algebraMap (CuspForm.heckeBaseAlgebra M' S 𝒪) (CuspForm.heckeLocal M' S 𝒪 θ')
        (a ⊗ₜ[ℤ] CuspForm.latticeRestrictHom M' S t)) =
      g' (algebraMap (CuspForm.heckeBaseAlgebra M' S 𝒪) (CuspForm.heckeLocal M' S 𝒪 θ')
        (a ⊗ₜ[ℤ] CuspForm.latticeRestrictHom M' S t))
    rw [hsplit]
    simp only [map_mul]
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes, AlgHom.commutes]
    exact congrArg (algebraMap 𝒪 A a * ·) (RingHom.congr_fun hπ t)
  apply AlgHom.coe_ringHom_injective
  exact IsLocalization.ringHom_ext (CuspForm.heckeLocalSubmonoid M' S 𝒪 θ') hbase

end Lattice

end PsiAnemic

open IsLocalRing

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (S : Set ℕ) (M M' : ℕ) [NeZero M] [NeZero M'] [Fact (CuspForm.HasIntegralStructure M' 2)]
    (hMM' : M ∣ M')
    (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (θ : CuspForm.heckeAlgebra M 2 S →+* ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra M' 2 S →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S),
      θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS) =
        θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS)) :
    ∃ Ψ : CuspForm.heckeLocal M' S 𝒪 θ' →ₐ[𝒪] CuspForm.heckeLocal M S 𝒪 θ,
      Function.Surjective Ψ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S),
        Ψ (CuspForm.heckeLocal.π M' S 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS)) =
          CuspForm.heckeLocal.π M S 𝒪 θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS)) ∧
      (∀ (A : Type) [CommRing A] [Algebra 𝒪 A]
        (f : CuspForm.heckeLocal M S 𝒪 θ →ₐ[𝒪] A) (g : CuspForm.heckeLocal M' S 𝒪 θ' →ₐ[𝒪] A),
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S),
          g (CuspForm.heckeLocal.π M' S 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS)) =
            f (CuspForm.heckeLocal.π M S 𝒪 θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS))) →
        g = f.comp Ψ) := by
  have hθθ' := PsiAnemic.theta'_eq hMM' hS θ θ' hθ
  refine ⟨PsiAnemic.Ψ 𝒪 θ θ' hMM' hS hθθ', PsiAnemic.Ψ_surjective 𝒪 θ θ' hMM' hS hθθ',
    fun ℓ hℓ hℓM' hℓS => PsiAnemic.Ψ_π_T 𝒪 θ θ' hMM' hS hθθ' hℓ hℓM' hℓS, ?_⟩
  intro A _ _ f g h
  exact PsiAnemic.ext_π_T 𝒪 θ' hS g (f.comp (PsiAnemic.Ψ 𝒪 θ θ' hMM' hS hθθ'))
    (fun ℓ hℓ hℓM' hℓS => by rw [AlgHom.comp_apply, PsiAnemic.Ψ_π_T]; exact h ℓ hℓ hℓM' hℓS)

end S_CuspForm_heckeLocal_exists_surjective_algHom_apply_pi_T_eq_of_dvd
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_surjective_algHom_apply_pi_T_eq_of_dvd (solution)
