-- Prove2me | solution 1 for CuspForm.exists_gamma1_coe_eq_and_hasNebentypus_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/211da107-c81c-5b67-a43c-a363e561df21

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

namespace Ws41
namespace B4

open CongruenceSubgroup
open scoped MatrixGroups

theorem gamma1GL_le_gamma0GL (M : ℕ) :
    ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma1_in_Gamma0 M)

noncomputable def gamma1View {M : ℕ} {k : ℤ} (g : CuspForm (Gamma0 M) k) : CuspForm (Gamma1 M) k where
  toFun := g
  slash_action_eq' A hA := g.slash_action_eq' A (gamma1GL_le_gamma0GL M hA)
  holo' := g.holo'
  zero_at_cusps' hc := g.zero_at_cusps' (hc.mono (gamma1GL_le_gamma0GL M))

@[scoped simp] theorem coe_gamma1View {M : ℕ} {k : ℤ} (g : CuspForm (Gamma0 M) k) :
    (⇑(gamma1View g) : UpperHalfPlane → ℂ) = ⇑g := rfl

theorem isUnit_entry_one_one_of_mem_Gamma0 {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    IsUnit (((γ 1 1 : ℤ) : ZMod M)) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := by
    have := Gamma0_mem.mp hγ
    exact_mod_cast this
  have h : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hc, mul_zero, sub_zero] at this
    exact this
  exact IsUnit.of_mul_eq_one_right _ h

theorem hasNebentypus_one_of_coe_eq {M : ℕ} {k : ℤ} (g : CuspForm (Gamma0 M) k)
    (g₁ : CuspForm (Gamma1 M) k) (hg₁ : (⇑g₁ : UpperHalfPlane → ℂ) = ⇑g) :
    CuspForm.HasNebentypus (1 : DirichletCharacter ℂ M) g₁ := by
  intro γ hγ τ
  rw [MulChar.one_apply (isUnit_entry_one_one_of_mem_Gamma0 hγ), one_mul]
  have h1 := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  rw [show g₁ (γ • τ) = g (γ • τ) from congrFun hg₁ _, show g₁ τ = g τ from congrFun hg₁ _, h1]
  congr 1

end Ws41.B4
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one.Ws41 P2MW.S_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one.Ws41.B4"
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one.Ws41"

theorem solution
    {M : ℕ} (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g₁ : CuspForm (CongruenceSubgroup.Gamma1 M) k,
      (⇑g₁ : UpperHalfPlane → ℂ) = ⇑g ∧ CuspForm.HasNebentypus (1 : DirichletCharacter ℂ M) g₁ :=
  ⟨Ws41.B4.gamma1View g, rfl, Ws41.B4.hasNebentypus_one_of_coe_eq g _ rfl⟩

end S_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one
end P2MW
export P2MW.S_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one (solution)
