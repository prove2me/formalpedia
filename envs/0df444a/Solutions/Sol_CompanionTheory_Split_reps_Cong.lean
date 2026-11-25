-- Prove2me | solution 1 for CompanionTheory.Split.reps_Cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:10.812665+00:00
-- url     : https://prove2.me/submissions/58692b7e-ef7a-4c89-ae96-3b0ac420007d

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_CompanionTheory_Split_ALint_eq
import Theorems.Thm_CompanionTheory_Split_levelafC_nat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_levelaf_finite_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
namespace CompanionTheory.Split
theorem _root_.solution {N : ℕ} (hN : N ≠ 0) :
    ∃ T : Set (GA L n), T.Finite ∧ ∀ u ∈ Umax L n, ∃ t ∈ T, NG.Cong L n N (t⁻¹ * u) := by
  have hfin : Finite (ALint L ⧸ Ideal.span {(N : ALint L)}) := by
    have := P.levelaf_finite_quot (F := L⁺) (E := L) (N : 𝓞 L⁺) (Nat.cast_ne_zero.2 hN) N
      (by rw [levelafC_nat]; rfl)
    rwa [← ALint_eq] at this
  let red : Umax L n → Fin n → Fin n → ALint L ⧸ Ideal.span {(N : ALint L)} := fun u i j =>
    Ideal.Quotient.mk _ ⟨_, u.2 i j⟩
  refine ⟨Set.range fun m => (Function.invFun red m : Umax L n), Set.finite_range _, fun u hu => ?_⟩
  set t := Function.invFun red (red ⟨u, hu⟩) with ht
  have e : red t = red ⟨u, hu⟩ := Function.invFun_eq ⟨_, rfl⟩
  refine ⟨t, ⟨_, rfl⟩, (Umax L n).mul_mem ((Umax L n).inv_mem t.2) hu, fun i j => ?_⟩
  choose y hy using fun a b => Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun e.symm a) b))
  refine ⟨∑ a, ent (t : GA L n)⁻¹ i a * y a j,
    Subring.sum_mem _ fun a _ => Subring.mul_mem _ ((Umax L n).inv_mem t.2 i a) (y a j).2, ?_⟩
  have h1 : ent (t : GA L n)⁻¹ * ent (t : GA L n) = 1 := congrArg ent (inv_mul_cancel (t : GA L n))
  show (ent (t : GA L n)⁻¹ * ent u) i j - _ = _
  rw [← h1, ← Matrix.sub_apply, ← Matrix.mul_sub, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (y a j : AL L) * N = ent u a j - ent (t : GA L n) a j := congrArg Subtype.val (hy a j)
  rw [Matrix.sub_apply, ← this]
  ring
end CompanionTheory.Split
