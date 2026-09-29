-- Prove2me | solution 1 for CohCarrier.exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5687a905-0b7c-50b5-b360-d81db899f81d

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute
import Theorems.Thm_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting

set_option autoImplicit false

open IsLocalRing
open scoped IsMulCommutative TensorProduct

namespace CohCarrier
p2m_export "CohCarrier" "Gen heckeTL heckeTL_apply opFamily hdata Gen.T Gen.U GammaH H1 heckeT exists_injective_linearMap_baseChange_H1_heckeTL H1_moduleFinite"
namespace CornerEigenAux
p2m_open "CohCarrier"

section LinAlg

variable {𝒪 : Type} [CommRing 𝒪] {V : Type} [AddCommGroup V] [Module 𝒪 V]
variable (K : Type) [Field K] [Algebra 𝒪 K]
variable (B : Subalgebra 𝒪 (Module.End 𝒪 V))

noncomputable def bc (b : B) : Module.End K (K ⊗[𝒪] V) := (b : Module.End 𝒪 V).baseChange K

theorem bc_mul (a b : B) : bc K B (a * b) = bc K B a * bc K B b := by
  unfold bc
  rw [Subalgebra.coe_mul, LinearMap.baseChange_mul]

theorem bc_one : bc K B 1 = 1 := by
  unfold bc
  rw [Subalgebra.coe_one, LinearMap.baseChange_one]

theorem bc_add (a b : B) : bc K B (a + b) = bc K B a + bc K B b := by
  unfold bc
  rw [Subalgebra.coe_add, LinearMap.baseChange_add]

theorem bc_zero : bc K B 0 = 0 := by
  unfold bc
  rw [Subalgebra.coe_zero, LinearMap.baseChange_zero]

theorem bc_tmul (b : B) (a : K) (v : V) : bc K B b (a ⊗ₜ[𝒪] v) = a ⊗ₜ[𝒪] ((b : Module.End 𝒪 V) v) := by
  unfold bc
  rw [LinearMap.baseChange_tmul]

theorem bc_mul_apply (a b : B) (x : K ⊗[𝒪] V) : bc K B (a * b) x = bc K B a (bc K B b x) := by
  rw [bc_mul]; rfl

theorem exists_ringHom_and_eigenvector [IsAlgClosed K] [Module.Finite K (K ⊗[𝒪] V)]
    (hcomm : ∀ a b : B, a * b = b * a) (e : B) (he : e * e = e)
    (hE : ∃ x : K ⊗[𝒪] V, bc K B e x ≠ 0) :
    ∃ (ψ : B →+* K) (w : K ⊗[𝒪] V), w ≠ 0 ∧ w ∈ LinearMap.range (bc K B e) ∧ ψ e = 1 ∧
      ∀ b : B, bc K B b w = ψ b • w := by
  classical
  set E : Submodule K (K ⊗[𝒪] V) := LinearMap.range (bc K B e) with hEdef

  have hinv : ∀ b : B, ∀ x ∈ E, bc K B b x ∈ E := by
    rintro b x ⟨y, rfl⟩
    refine ⟨bc K B b y, ?_⟩
    rw [← bc_mul_apply, hcomm e b, bc_mul_apply]
  let T : B → Module.End K E := fun b => (bc K B b).restrict (hinv b)
  have hTval : ∀ (b : B) (x : E), ((T b x : E) : K ⊗[𝒪] V) = bc K B b (x : K ⊗[𝒪] V) :=
    fun b x => rfl
  have hT : Pairwise fun a b => Commute (T a) (T b) := by
    intro a b _
    show T a * T b = T b * T a
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show bc K B a (bc K B b (x : K ⊗[𝒪] V)) = bc K B b (bc K B a (x : K ⊗[𝒪] V))
    rw [← bc_mul_apply, hcomm a b, bc_mul_apply]
  obtain ⟨x₀, hx₀⟩ := hE
  haveI : Nontrivial E :=
    nontrivial_of_ne (⟨bc K B e x₀, LinearMap.mem_range_self _ x₀⟩ : E) 0
      (fun h => hx₀ (congrArg Subtype.val h))
  obtain ⟨w, hw0, hw⟩ := Module.End.exists_forall_apply_eq_smul_of_pairwise_commute (V := ↥E) T hT
  choose ψf hψf using hw
  have hw0' : (w : K ⊗[𝒪] V) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hψ : ∀ b : B, bc K B b (w : K ⊗[𝒪] V) = ψf b • (w : K ⊗[𝒪] V) := by
    intro b
    have := congrArg Subtype.val (hψf b)
    simpa only [hTval, Submodule.coe_smul] using this
  have cancel : ∀ c d : K, c • (w : K ⊗[𝒪] V) = d • (w : K ⊗[𝒪] V) → c = d :=
    fun c d h => smul_left_injective K hw0' h

  have h1 : ψf 1 = 1 := by
    apply cancel
    rw [← hψ, bc_one, one_smul]
    rfl
  have hmul : ∀ a b : B, ψf (a * b) = ψf a * ψf b := by
    intro a b
    apply cancel
    rw [← hψ, bc_mul_apply, hψ b, LinearMap.map_smul, hψ a, smul_smul, mul_comm]
  have h0 : ψf 0 = 0 := by
    apply cancel
    rw [← hψ, bc_zero, zero_smul]
    rfl
  have hadd : ∀ a b : B, ψf (a + b) = ψf a + ψf b := by
    intro a b
    apply cancel
    rw [← hψ, bc_add, LinearMap.add_apply, hψ a, hψ b, add_smul]
  let ψ : B →+* K :=
    { toFun := ψf, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }

  have he1 : ψf e = 1 := by
    apply cancel
    rw [← hψ, one_smul]
    obtain ⟨y, hy⟩ := w.2
    rw [← hy, ← bc_mul_apply, he]
  exact ⟨ψ, w, hw0', w.2, he1, hψ⟩

end LinAlg

section Corner

variable {B : Type} [CommRing B] (Sp : IharaLemma.IdempotentSplitting B) (i : Fin Sp.n)
variable {K : Type} [CommRing K] (ψ : B →+* K) (hψ : ψ (Sp.e i) = 1)

def cornerHom : Sp.CornerRing i →+* K where
  toFun z := ψ (z : B)
  map_one' := by
    show ψ (Sp.e i) = 1
    exact hψ
  map_mul' z w := by
    show ψ ((z : B) * (w : B)) = ψ (z : B) * ψ (w : B)
    exact map_mul ψ _ _
  map_zero' := by
    show ψ 0 = 0
    exact map_zero ψ
  map_add' z w := by
    show ψ ((z : B) + (w : B)) = ψ (z : B) + ψ (w : B)
    exact map_add ψ _ _

theorem cornerHom_toCornerRing (b : B) : cornerHom Sp i ψ hψ (Sp.toCornerRing i b) = ψ b := by
  show ψ (Sp.e i * b * Sp.e i) = ψ b
  rw [map_mul, map_mul, hψ, one_mul, mul_one]

end Corner

end CohCarrier.CornerEigenAux

open CohCarrier.CornerEigenAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (hcomm : ∀ g h : CohCarrier.Gen L S,
      CohCarrier.opFamily L ⊤ S 𝒪 g * CohCarrier.opFamily L ⊤ S 𝒪 h =
        CohCarrier.opFamily L ⊤ S 𝒪 h * CohCarrier.opFamily L ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen L S → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (K : Type) [Field K] [IsAlgClosed K] [Algebra 𝒪 K]
    (hinj : Function.Injective (algebraMap 𝒪 K)) :
    ∃ (φ : Sp.CornerRing i₀ →+* K) (c : CohCarrier.H1 L ⊤ K), c ≠ 0 ∧
      ((∀ v : CohCarrier.H1 L ⊤ 𝒪,
          v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
            v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH L ⊤) 𝒪) →
        c ∈ ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH L ⊤) K) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT L ⊤ ℓ K c) =
          φ (Sp.toCornerRing i₀
            ⟨(CohCarrier.hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓL),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩) • c) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ L),
        (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeT L ⊤ q K c) =
          φ (Sp.toCornerRing i₀
            ⟨(CohCarrier.hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.U q hq hqL),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩) • c) := by
  classical
  let B : Subalgebra 𝒪 (Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) :=
    (CohCarrier.hdata L ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra

  haveI : Module.Finite 𝒪 (CohCarrier.H1 L ⊤ 𝒪) := CohCarrier.H1_moduleFinite L ⊤ 𝒪 𝒪
  haveI : Module.Finite K (K ⊗[𝒪] CohCarrier.H1 L ⊤ 𝒪) := inferInstance

  obtain ⟨j, hjinj, hjtmul, hjT⟩ :=
    CohCarrier.exists_injective_linearMap_baseChange_H1_heckeTL L ⊤ 𝒪 K

  have he0 : Sp.e i₀ ≠ 0 := by
    intro h
    apply Sp.notMem i₀
    rw [h]
    exact (Sp.𝔪 i₀).zero_mem
  have he0' : (Sp.e i₀ : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) ≠ 0 :=
    fun h => he0 (Subtype.ext h)
  have hE : ∃ x : K ⊗[𝒪] CohCarrier.H1 L ⊤ 𝒪, bc K B (Sp.e i₀) x ≠ 0 := by
    obtain ⟨v, hv⟩ : ∃ v, (Sp.e i₀ : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v ≠ 0 := by
      by_contra hall
      push Not at hall
      exact he0' (LinearMap.ext hall)
    obtain ⟨γ, hγ⟩ : ∃ γ, (Sp.e i₀ : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v γ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv (AddMonoidHom.ext hall)
    refine ⟨(1 : K) ⊗ₜ[𝒪] v, fun h0 => ?_⟩
    have h1 := congrArg j h0
    rw [bc_tmul, hjtmul, map_zero, one_smul] at h1
    have h2 := DFunLike.congr_fun h1 γ
    exact hγ (hinj (by rw [map_zero]; exact h2))

  obtain ⟨ψ, w, hw0, hwE, hψe, hψ⟩ :=
    exists_ringHom_and_eigenvector K B (fun a b => mul_comm a b) (Sp.e i₀) (Sp.idem i₀).eq hE

  have hparK : (∀ v : CohCarrier.H1 L ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH L ⊤) 𝒪) →
      ∀ x : K ⊗[𝒪] CohCarrier.H1 L ⊤ 𝒪,
        j (bc K B (Sp.e i₀) x) ∈ ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH L ⊤) K := by
    intro hpar x
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero]
      exact Submodule.zero_mem _
    | tmul a v =>
      rw [bc_tmul, hjtmul]
      refine Submodule.smul_mem _ a ?_
      have hv : (Sp.e i₀ : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v ∈
          ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH L ⊤) 𝒪 :=
        hpar ((Sp.e i₀ : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v) ⟨v, rfl⟩
      rw [ModularCurve.Period.mem_parabolicHoms_iff] at hv ⊢
      intro γ hγ
      show algebraMap 𝒪 K ((Sp.e i₀ : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v (Additive.ofMul γ)) = 0
      rw [hv γ hγ, map_zero]
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy

  have hclause : ∀ (ℓ : ℕ) (hℓ0 : NeZero ℓ) (g : B),
      (g : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) = CohCarrier.heckeTL L ⊤ 𝒪 ℓ →
      CohCarrier.heckeT L ⊤ ℓ K (j w) = cornerHom Sp i₀ ψ hψe (Sp.toCornerRing i₀ g) • j w := by
    intro ℓ _ g hg
    calc CohCarrier.heckeT L ⊤ ℓ K (j w)
        = CohCarrier.heckeTL L ⊤ K ℓ (j w) := (CohCarrier.heckeTL_apply L ⊤ K ℓ (j w)).symm
      _ = j ((CohCarrier.heckeTL L ⊤ 𝒪 ℓ).baseChange K w) := (hjT ℓ w).symm
      _ = j (bc K B g w) := by rw [← hg]; rfl
      _ = j (ψ g • w) := by rw [hψ g]
      _ = ψ g • j w := map_smul j _ _
      _ = cornerHom Sp i₀ ψ hψe (Sp.toCornerRing i₀ g) • j w := by
          rw [cornerHom_toCornerRing Sp i₀ ψ hψe g]

  refine ⟨cornerHom Sp i₀ ψ hψe, j w, fun h => hw0 (hjinj (by rw [h, map_zero])), ?_, ?_, ?_⟩
  · intro hpar
    obtain ⟨x, hx⟩ := hwE
    rw [← hx]
    exact hparK hpar x
  · intro ℓ hℓ hℓS hℓL
    exact hclause ℓ ⟨hℓ.ne_zero⟩ _ rfl
  · intro q hq hqL
    exact hclause q ⟨hq.ne_zero⟩ _ rfl

end S_CohCarrier_exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting
end P2MW
export P2MW.S_CohCarrier_exists_ringHom_cornerRing_heckeT_eq_smul_of_idempotentSplitting (solution)
