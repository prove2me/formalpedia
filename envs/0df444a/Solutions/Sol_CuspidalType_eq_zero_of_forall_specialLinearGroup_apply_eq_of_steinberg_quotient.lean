-- Prove2me | solution 1 for CuspidalType.eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7a0f1841-42ae-5aab-b80f-fd9ceabeb2b0

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient

set_option autoImplicit false

open scoped MatrixGroups

namespace CuspidalType
p2m_export "CuspidalType" "GL2 ProjLine ind steinberg constFun"
p2m_open "CuspidalType"
namespace SteinbergQuotientFixed

p2m_open "CuspidalType P2MW.S_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient.CuspidalType"

variable {q : ℕ} [Fact q.Prime]

theorem smul_mk_eq (g : GL2 q) (u : Fin 2 → ZMod q) (hu : u ≠ 0) :
    ∃ h, g • Projectivization.mk (ZMod q) u hu =
      Projectivization.mk (ZMod q) ((g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec u) h := by
  refine ⟨?_, ?_⟩
  swap
  · change (Matrix.GeneralLinearGroup.toLin g) • Projectivization.mk (ZMod q) u hu = _
    rw [Projectivization.smul_mk]
    congr 1
  · intro h0
    apply hu
    have := congrArg (((g⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q))).mulVec h0
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this

theorem exists_sl_fixed_smul_eq (y z : ProjLine q) :
    ∃ g : SL(2, ZMod q), (∃ x : ProjLine q, Matrix.SpecialLinearGroup.toGL g • x = x) ∧
      Matrix.SpecialLinearGroup.toGL g • y = z := by
  classical
  by_cases hyz : y = z
  · exact ⟨1, ⟨y, by simp⟩, by simp [hyz]⟩

  have hind : LinearIndependent (ZMod q) ![y.rep, z.rep] := by
    have := (Projectivization.independent_pair_iff_ne y z).2 hyz
    rw [Projectivization.independent_iff] at this
    convert this using 1
    ext i : 1
    fin_cases i <;> rfl
    rfl
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod q) (Fin 2 → ZMod q) := by simp
  set b : Module.Basis (Fin 2) (ZMod q) (Fin 2 → ZMod q) :=
    basisOfLinearIndependentOfCardEqFinrank hind hcard with hb
  have hb0 : b 0 = y.rep := by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hb1 : b 1 = z.rep := by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl

  set f : (Fin 2 → ZMod q) →ₗ[ZMod q] (Fin 2 → ZMod q) :=
    b.constr (ZMod q) ![b 1, -b 0 + (2 : ZMod q) • b 1] with hf
  have hf0 : f (b 0) = b 1 := by
    rw [hf, Module.Basis.constr_basis]; rfl
  have hf1 : f (b 1) = -b 0 + (2 : ZMod q) • b 1 := by
    rw [hf, Module.Basis.constr_basis]; rfl
  have hdet : LinearMap.det f = 1 := by
    rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply]
    rw [show (0 : Fin 2) = 0 from rfl]
    have e0 : b.repr (f (b 0)) = Finsupp.single 1 1 := by rw [hf0, b.repr_self]
    have e1 : b.repr (f (b 1)) = -Finsupp.single 0 1 + (2 : ZMod q) • Finsupp.single 1 1 := by
      rw [hf1, map_add, map_neg, map_smul, b.repr_self, b.repr_self]
    rw [e0, e1]
    simp
  let g : SL(2, ZMod q) := ⟨LinearMap.toMatrix' f, by rw [LinearMap.det_toMatrix']; exact hdet⟩
  have hgmul : ∀ u, (((Matrix.SpecialLinearGroup.toGL g : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q))).mulVec u
      = f u := fun u => LinearMap.toMatrix'_mulVec f u
  have hne : b 1 - b 0 ≠ 0 := sub_ne_zero.2 (b.injective.ne (by decide))
  refine ⟨g, ⟨Projectivization.mk (ZMod q) (b 1 - b 0) hne, ?_⟩, ?_⟩
  · obtain ⟨h, hh⟩ := smul_mk_eq (Matrix.SpecialLinearGroup.toGL g) (b 1 - b 0) hne
    rw [hh]
    simp_rw [hgmul]
    congr 1
    rw [map_sub, hf0, hf1]
    module
  · conv_lhs => rw [← y.mk_rep]
    obtain ⟨h, hh⟩ := smul_mk_eq (Matrix.SpecialLinearGroup.toGL g) y.rep y.rep_nonzero
    rw [hh, ← z.mk_rep]
    simp_rw [hgmul]
    congr 1
    rw [← hb0, hf0, hb1]

variable (q) (κ : Type) [Field κ]

theorem ind_apply_apply (g : GL2 q) (s : ProjLine q →₀ κ) (x : ProjLine q) :
    (ind q κ g s) x = s (g⁻¹ • x) := by
  rw [Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply]
  conv_lhs => rw [← smul_inv_smul g x]
  rw [Finsupp.mapDomain_apply (MulAction.injective g)]

variable {κ}
variable {V : Type} [AddCommGroup V] [Module κ V]

theorem main
    (ρ : Representation κ (GL2 q) V)
    (π : ↥(steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : GL2 q, ∀ v : ↥(steinberg q κ).toSubmodule,
      π ⟨ind q κ g v, (steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(steinberg q κ).toSubmodule,
      π v = 0 ↔ ∃ c : κ, (v : ProjLine q →₀ κ) = c • constFun q κ)
    (v : V) (hv : ∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) : v = 0 := by
  classical
  obtain ⟨s, rfl⟩ := hπsurj v

  have hc : ∀ g : SL(2, ZMod q), ∃ c : κ, ∀ x : ProjLine q,
      (s : ProjLine q →₀ κ) ((Matrix.SpecialLinearGroup.toGL g)⁻¹ • x) - (s : ProjLine q →₀ κ) x = c := by
    intro g
    have hmem := (steinberg q κ).apply_mem_toSubmodule (Matrix.SpecialLinearGroup.toGL g) s.2
    have hπt : π (⟨_, hmem⟩ - s) = 0 := by
      have e := map_sub π ⟨_, hmem⟩ s
      rw [hπ, hv g, sub_self] at e
      exact e
    obtain ⟨c, hct⟩ := (hπker _).1 hπt
    refine ⟨c, fun x => ?_⟩
    have := congrArg (fun φ : ProjLine q →₀ κ => φ x) hct
    simp only [Submodule.coe_sub, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul] at this
    rw [ind_apply_apply] at this
    rw [this]
    simp [constFun]

  have hfix : ∀ g : SL(2, ZMod q), ∀ x₀ : ProjLine q, Matrix.SpecialLinearGroup.toGL g • x₀ = x₀ →
      ∀ x : ProjLine q, (s : ProjLine q →₀ κ) (Matrix.SpecialLinearGroup.toGL g • x)
        = (s : ProjLine q →₀ κ) x := by
    intro g x₀ hx₀ x
    obtain ⟨c, hcg⟩ := hc g
    have h0 : c = 0 := by
      rw [← hcg x₀]
      conv_lhs => rw [← hx₀, inv_smul_smul, hx₀]
      exact sub_self _
    have := hcg (Matrix.SpecialLinearGroup.toGL g • x)
    rw [inv_smul_smul, h0, sub_eq_zero] at this
    exact this.symm

  have hconst : ∀ y z : ProjLine q, (s : ProjLine q →₀ κ) y = (s : ProjLine q →₀ κ) z := by
    intro y z
    obtain ⟨g, ⟨x₀, hx₀⟩, hyz⟩ := exists_sl_fixed_smul_eq y z
    rw [← hyz, hfix g x₀ hx₀]

  have x₀ : ProjLine q := Projectivization.mk (ZMod q) (Pi.single 0 1) (by simp)
  apply (hπker s).2
  refine ⟨(s : ProjLine q →₀ κ) x₀, ?_⟩
  ext x
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, constFun,
    Finsupp.coe_equivFunOnFinite_symm, mul_one]
  exact hconst x x₀

end SteinbergQuotientFixed
end CuspidalType

open scoped MatrixGroups in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (κ : Type) [Field κ] (hq1 : (q : κ) + 1 = 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ) :
    ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0 :=
  CuspidalType.SteinbergQuotientFixed.main q ρ π hπ hπsurj hπker

end S_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient
end P2MW
export P2MW.S_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient (solution)
