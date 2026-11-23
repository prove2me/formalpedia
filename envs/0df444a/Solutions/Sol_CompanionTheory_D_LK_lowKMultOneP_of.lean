-- Prove2me | solution 1 for CompanionTheory.D.LK.lowKMultOneP_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:24.645963+00:00
-- url     : https://prove2.me/submissions/255255ee-085f-4973-b195-9d70636bfa60

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply


section
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace CompanionTheory.D.LK
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight CasK Cas)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsDS rhoC)
open CompanionTheory.D.DSIC (KRel KUnit KStab LowSpan HWMap)
variable {n : ℕ}
section
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end
private lemma commute_E_cas_of_glRel {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (c d : Fin n) :
    E c d * Cas E = Cas E * E c d := by
  rw [← sub_eq_zero]
  have hsplit : E c d * Cas E - Cas E * E c d =
      (∑ a, ∑ b, (if d = a then E c b else 0) * E b a) - (∑ a, ∑ b, (if b = c then E a d else 0) * E b a)
      + ((∑ a, ∑ b, E a b * (if d = b then E c a else 0)) - (∑ a, ∑ b, E a b * (if a = c then E b d else 0))) := by
    simp only [Formalism.REAL.Cas, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [← sub_mul, ← mul_sub, ← hE c d a b, ← hE c d b a]
    noncomm_ring
  have T1 : (∑ a, ∑ b, (if d = a then E c b else 0) * E b a) = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have T2 : (∑ a, ∑ b, (if b = c then E a d else 0) * E b a) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have T3 : (∑ a, ∑ b, E a b * (if d = b then E c a else 0)) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have T4 : (∑ a, ∑ b, E a b * (if a = c then E b d else 0)) = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsplit, T1, T2, T3, T4]
  abel
end CompanionTheory.D.LK
end
end

set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight CasK Cas)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsDS rhoC)
open CompanionTheory.D.DSIC (KRel KUnit KStab LowSpan HWMap)
variable {n : ℕ}
namespace CompanionTheory.D.LK
theorem _root_.solution (hM : MultAlg) (hE : KModExists) (hD : CycDense) (hO : OrthCyc) : LowKMultOneP := by
  intro N ε lam H _ _ σ hHC hDS S S' hS hS'
  obtain ⟨hcomp, -, hUR, hIR, -, -, hmin⟩ := hDS
  haveI := hcomp
  obtain ⟨D, E, hK⟩ := hE N ε H σ hUR hIR
  have hGl : GlRel E := hK.gl
  have hU : CompanionTheory.D.DSIC.KUnit ε E := by
    intro a b h x y
    rw [hK.unit a b x y]
    simp only [Formalism.REAL.sgn, if_pos h, Complex.ofReal_one, one_mul]
  have hLF : CompanionTheory.D.LK.LocFin ε E := hK.locFin
  have hIM : CompanionTheory.D.LK.IsMin ε E lam := by
    intro μ x hx hxh
    obtain ⟨T, hT⟩ := hK.ty μ x hx hxh
    exact hmin μ T hT
  obtain ⟨v, hv0, hvS, hv⟩ := hK.hw _ S hS
  obtain ⟨v', hv'0, hv'S, hv'⟩ := hK.hw _ S' hS'
  have hmult : ∀ w, KHighest ε E (lowK ε lam) w → w ∈ Cyc E v → ∃ c : ℂ, w = c • v :=
    fun w hw hwc => hM N ε lam D E hHC.1 hGl hU hLF hIM v w hv0 hv hw hwc
  have hcv : KHighest ε E (lowK ε lam) (Cas E v) := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · rw [← Module.End.mul_apply, commute_E_cas_of_glRel E hGl a a, Module.End.mul_apply, hv.1 a, map_smul]
    · rw [← Module.End.mul_apply, commute_E_cas_of_glRel E hGl a b, Module.End.mul_apply, hv.2 a b hab h, map_zero]
  have hcc : Cas E v ∈ Cyc E v := by
    refine mem_cyc.2 ⟨∑ a, ∑ b, FreeAlgebra.ι ℂ (a, b) * FreeAlgebra.ι ℂ (b, a), ?_⟩
    simp only [CompanionTheory.D.LK.ev, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Formalism.REAL.Cas]
  obtain ⟨c, hc⟩ := hmult _ hcv hcc
  have hdense := hD N ε H σ D E hUR hIR hK v c hv0 hc
  set u : D := inner ℂ v v • v' - inner ℂ v v' • v with hu_def
  have hu : KHighest ε E (lowK ε lam) u := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · rw [hu_def, map_sub, map_smul, map_smul, hv'.1 a, hv.1 a, smul_sub, smul_smul, smul_smul,
        smul_smul, smul_smul, mul_comm (inner ℂ v v), mul_comm (inner ℂ v v')]
    · rw [hu_def, map_sub, map_smul, map_smul, hv'.2 a b hab h, hv.2 a b hab h, smul_zero, smul_zero, sub_zero]
  have horth0 : inner ℂ v u = 0 := by
    rw [hu_def, inner_sub_right, inner_smul_right, inner_smul_right]
    ring
  have horth := hO N ε D E (lowK ε lam) v u hGl hU hLF (fun w hwc hw => hmult w hw hwc) hu horth0
  have hsub : Submodule.map D.subtype (Cyc E v) ≤ (ℂ ∙ (u : H))ᗮ := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact (Submodule.coe_inner D m u).symm.trans (horth m hm)
  have hcl := Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_orthogonal _)
  rw [hdense] at hcl
  have hum : (u : H) ∈ (ℂ ∙ (u : H))ᗮ := hcl Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_self_eq_zero] at hum
  have hu0 : u = 0 := Subtype.ext hum
  have hvv : inner ℂ v v ≠ 0 := inner_self_ne_zero.2 hv0
  have heq : inner ℂ v v • v' = inner ℂ v v' • v := sub_eq_zero.1 (hu_def ▸ hu0)
  have hv'S2 : (v' : H) ∈ S := by
    have e : v' = ((inner ℂ v v)⁻¹ * inner ℂ v v') • v := by
      rw [mul_smul, ← heq, smul_smul, inv_mul_cancel₀ hvv, one_smul]
    rw [e, Submodule.coe_smul]
    exact S.smul_mem _ hvS
  have hinf : PI.UpqRep.IsKStableOn ε σ (S ⊓ S') :=
    fun g hg x hx => ⟨hS.2.1 g hg x hx.1, hS'.2.1 g hg x hx.2⟩
  have hvne : (v : H) ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have hv'ne : (v' : H) ≠ 0 := fun h0 => hv'0 (Subtype.ext h0)
  rcases hS.2.2.1 (S ⊓ S') inf_le_left hinf with h | h
  · exfalso
    have hm : (v' : H) ∈ S ⊓ S' := ⟨hv'S2, hv'S⟩
    rw [h] at hm
    exact hv'ne ((Submodule.mem_bot ℂ).1 hm)
  · have hle : S ≤ S' := h ▸ inf_le_right
    rcases hS'.2.2.1 S hle hS.2.1 with h2 | h2
    · exfalso
      have hm : (v : H) ∈ S := hvS
      rw [h2] at hm
      exact hvne ((Submodule.mem_bot ℂ).1 hm)
    · exact h2
end CompanionTheory.D.LK
