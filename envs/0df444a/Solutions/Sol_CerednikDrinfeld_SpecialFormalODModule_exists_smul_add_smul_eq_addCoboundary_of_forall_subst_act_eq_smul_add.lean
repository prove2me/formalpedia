-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d7985391-4627-5c1a-8316-8d98a20842d0

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_forall_exists_subst_act_subst_varpi_eq_smul_of_type
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow Cob.PA"
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R]

namespace C1Kit

variable {τ : Type*} (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}

theorem constantCoeff_XL (l : Fin g) :
    constantCoeff ((fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) l) = 0 :=
  constantCoeff_X _

theorem constantCoeff_XR (l : Fin g) :
    constantCoeff ((fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) l) = 0 :=
  constantCoeff_X _

theorem symm_elim (hΓ : F.IsSymmTwoCocycle Γ) {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    subst (Sum.elim b a) Γ = subst (Sum.elim a b) Γ := by
  have hT : HasSubst (Sum.elim a b) := hasSubst_elim ha hb
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  have key := congrArg (subst (R := R) (Sum.elim a b)) hΓ.symm
  rw [subst_comp_subst_apply hswap hT] at key
  have hfam : (fun s => subst (Sum.elim a b) ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s)) = Sum.elim b a := by
    funext s
    rcases s with j | j <;> simp [subst_X hT]
  rw [hfam] at key
  exact key

theorem cocycle_elim (hΓ : F.IsSymmTwoCocycle Γ) {a b c : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c) Γ
        + subst (Sum.elim a b) Γ
      = subst (Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j)) Γ
        + subst (Sum.elim b c) Γ := by
  have hT0 : ∀ s : Fin g ⊕ (Fin g ⊕ Fin g),
      ((Sum.elim a (Sum.elim b c)) s).constantCoeff = 0 := by
    rintro (j | j | j)
    exacts [ha j, hb j, hc j]
  have hT : HasSubst (Sum.elim a (Sum.elim b c)) := hasSubst_of_constantCoeff_zero hT0
  have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hB := hasSubst_of_constantCoeff_zero hzB
  have hC := hasSubst_of_constantCoeff_zero hzC
  have hA : HasSubst (Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero hB hzB (F.constantCoeff_eq_zero j)
    · exact constantCoeff_X _
  have hA' : HasSubst (Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_X _
    · exact constantCoeff_subst_eq_zero hC hzC (F.constantCoeff_eq_zero j)
  have key := congrArg (subst (R := R) (Sum.elim a (Sum.elim b c))) hΓ.cocycle
  rw [subst_add hT, subst_add hT, subst_comp_subst_apply hA hT, subst_comp_subst_apply hA' hT,
    subst_comp_subst_apply hB hT, subst_comp_subst_apply hC hT] at key
  have hBfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) t)) = Sum.elim a b := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hCfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) t)) = Sum.elim b c := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hAfam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) s))
      = Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        = subst (Sum.elim a b) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hB hT, hBfam]
    · simp [subst_X hT]
  have hA'fam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) s))
      = Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j) := by
    funext s
    rcases s with j | j
    · simp [subst_X hT]
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
        = subst (Sum.elim b c) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hC hT, hCfam]
  rw [hAfam, hA'fam, hBfam, hCfam] at key
  exact key

theorem four_term [IsComm F] (hΓ : F.IsSymmTwoCocycle Γ) {a b c d : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) (hd : ∀ i, (d i).constantCoeff = 0) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j))
        fun j => subst (Sum.elim c d) (F.toPowerSeries j)) Γ
        + subst (Sum.elim a b) Γ + subst (Sum.elim c d) Γ
      = subst (Sum.elim (fun j => subst (Sum.elim a c) (F.toPowerSeries j))
        fun j => subst (Sum.elim b d) (F.toPowerSeries j)) Γ
        + subst (Sum.elim a c) Γ + subst (Sum.elim b d) Γ := by
  have hab := constantCoeff_subst_elim F ha hb
  have hac := constantCoeff_subst_elim F ha hc
  have e1 := cocycle_elim F hΓ hab hc hd
  have e2 := cocycle_elim F hΓ hac hb hd
  have e3 := cocycle_elim F hΓ ha hb hc
  have e4 := cocycle_elim F hΓ ha hc hb
  have hcb : (fun j => subst (Sum.elim c b) (F.toPowerSeries j))
      = fun j => subst (Sum.elim b c) (F.toPowerSeries j) :=
    funext fun j => subst_elim_comm F hc hb j
  rw [hcb, symm_elim F hΓ hb hc] at e4
  have h6 : (fun j => subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c)
        (F.toPowerSeries j))
      = fun j => subst (Sum.elim (fun j => subst (Sum.elim a c) (F.toPowerSeries j)) b)
        (F.toPowerSeries j) := by
    funext j
    rw [subst_elim_assoc F ha hb hc j, ← hcb, ← subst_elim_assoc F ha hc hb j]
  rw [h6] at e1
  linear_combination e2 - e1 + e3 - e4

end C1Kit

end MvFormalGroup

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow Cob.PA"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}

noncomputable abbrev inL (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R :=
  fun i => subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ i)

noncomputable abbrev inR (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R :=
  fun i => subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ i)

theorem hasSubst_XL : HasSubst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

variable {φ ψ : Fin g → MvPowerSeries (Fin g) R}

theorem constantCoeff_inL (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (inL φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) (hφ i)

theorem constantCoeff_inR (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (inR φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) (hφ i)

theorem inL_addVia (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) :
    inL (fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
      = fun i => subst (Sum.elim (inL φ) (inL ψ)) (F.toPowerSeries i) := by
  funext i
  show subst _ (subst (Sum.elim φ ψ) (F.toPowerSeries i)) = _
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XL]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem inR_addVia (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) :
    inR (fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
      = fun i => subst (Sum.elim (inR φ) (inR ψ)) (F.toPowerSeries i) := by
  funext i
  show subst _ (subst (Sum.elim φ ψ) (F.toPowerSeries i)) = _
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XR]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_XL_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (inL φ) (inL ψ)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XL]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_XR_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (inR φ) (inR ψ)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XR]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_law_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (hψF : ∀ i, subst F.toPowerSeries (ψ i) = subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i))
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst F.toPowerSeries (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (fun i => subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
          fun i => subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) F.hasSubst_toPowerSeries]
  congr 1
  funext s; rcases s with j | j
  · exact hφF j
  · exact hψF j

theorem pull_addVia [IsComm F] (hΓ : F.IsSymmTwoCocycle Γ)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (hψF : ∀ i, subst F.toPowerSeries (ψ i) = subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i)) :
    subst (Sum.elim (inL fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
        (inR fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))) Γ
      = subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL ψ) (inR ψ)) Γ
        + F.addCoboundary (subst (Sum.elim φ ψ) Γ) := by
  rw [inL_addVia F hφ hψ, inR_addVia F hφ hψ, addCoboundary, subst_law_subst_elim F hφ hψ hφF hψF,
    subst_XL_subst_elim hφ hψ, subst_XR_subst_elim hφ hψ]
  have h4 := four_term F hΓ (constantCoeff_inL hφ) (constantCoeff_inL hψ) (constantCoeff_inR hφ)
    (constantCoeff_inR hψ)
  linear_combination h4

theorem constantCoeff_subst_elim_cocycle (hΓ : F.IsSymmTwoCocycle Γ) {τ : Type*}
    {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    (subst (Sum.elim a b) Γ).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim ha hb) (by rintro (s | s); exacts [ha s, hb s])
    hΓ.constantCoeff_eq_zero

end MvFormalGroup.C1Kit

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormalODModule FormalODModule.forall_exists_subst_act_subst_varpi_eq_smul_of_type SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary" namespace FormalODModule p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi forall_exists_subst_act_subst_varpi_eq_smul_of_type" end CerednikDrinfeld.FormalODModule
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalODModule" in
open MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup MvFormalGroup.C1Kit _root_.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.exists_pull_act_add
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k]
    (X₀ : FormalODModule q k) (a b : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k)
    (hΓ : X₀.F.IsSymmTwoCocycle Γ) :
    ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      subst (Sum.elim (inL (X₀.act (a + b))) (inR (X₀.act (a + b)))) Γ
        = subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) Γ
          + subst (Sum.elim (inL (X₀.act b)) (inR (X₀.act b))) Γ + X₀.F.addCoboundary g := by
  haveI := X₀.isComm
  refine ⟨subst (Sum.elim (X₀.act a) (X₀.act b)) Γ,
    constantCoeff_subst_elim_cocycle X₀.F hΓ (X₀.isLawHom_act a).1 (X₀.isLawHom_act b).1, ?_⟩
  rw [X₀.act_add]
  exact pull_addVia X₀.F hΓ (X₀.isLawHom_act a).1 (X₀.isLawHom_act b).1 (X₀.isLawHom_act a).2
    (X₀.isLawHom_act b).2

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow Cob.PA"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}
variable {φ ψ : Fin g → MvPowerSeries (Fin g) R}

theorem subst_subst_pull {τ : Type*} {T : Fin g ⊕ Fin g → MvPowerSeries τ R} (hT : HasSubst T)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst T (subst (Sum.elim (inL φ) (inR φ)) f)
      = subst (Sum.elim (fun i => subst (fun m => T (Sum.inl m)) (φ i))
          fun i => subst (fun m => T (Sum.inr m)) (φ i)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)) hT]
  congr 1
  funext s; rcases s with j | j
  · show subst T (subst _ (φ j)) = _
    rw [subst_comp_subst_apply hasSubst_XL hT]
    congr 1; funext m; exact subst_X hT _
  · show subst T (subst _ (φ j)) = _
    rw [subst_comp_subst_apply hasSubst_XR hT]
    congr 1; funext m; exact subst_X hT _

theorem pull_comp (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL fun i => subst ψ (φ i)) (inR fun i => subst ψ (φ i))) f
      = subst (Sum.elim (inL ψ) (inR ψ)) (subst (Sum.elim (inL φ) (inR φ)) f) := by
  rw [subst_subst_pull (hasSubst_elim (constantCoeff_inL hψ) (constantCoeff_inR hψ)) hφ]
  congr 1
  funext s; rcases s with j | j
  · show subst _ (subst ψ (φ j)) = _
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ) hasSubst_XL]
    rfl
  · show subst _ (subst ψ (φ j)) = _
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ) hasSubst_XR]
    rfl

theorem pull_X (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL fun i => (X i : MvPowerSeries (Fin g) R)) (inR fun i => X i)) f = f := by
  have h : Sum.elim (inL fun i => (X i : MvPowerSeries (Fin g) R)) (inR fun i => X i)
      = (X : Fin g ⊕ Fin g → MvPowerSeries (Fin g ⊕ Fin g) R) := by
    funext s; rcases s with j | j
    · exact subst_X hasSubst_XL j
    · exact subst_X hasSubst_XR j
  rw [h, subst_self]; rfl

theorem symm_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0) :
    subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) fun j => X (Sum.inl j))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      = subst (Sum.elim (inL φ) (inR φ)) Γ := by
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  rw [subst_subst_pull hswap hφ]
  exact symm_elim F hΓ (constantCoeff_inL hφ) (constantCoeff_inR hφ)

section ThreeBlocks

noncomputable abbrev B1 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inl l)
noncomputable abbrev B2 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inr (Sum.inl l))
noncomputable abbrev B3 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inr (Sum.inr l))

theorem cB1 (l : Fin g) : ((B1 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _
theorem cB2 (l : Fin g) : ((B2 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _
theorem cB3 (l : Fin g) : ((B3 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _

noncomputable abbrev atB (B : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)
    (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R :=
  fun i => subst B (φ i)

theorem constantCoeff_atB {B : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R}
    (hB : ∀ l, (B l).constantCoeff = 0) (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (atB B φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hB) hB (hφ i)

theorem subst_lawpair (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    {Bi Bj : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R}
    (hBi : ∀ l, (Bi l).constantCoeff = 0) (hBj : ∀ l, (Bj l).constantCoeff = 0) (i : Fin g) :
    subst (fun m => subst (Sum.elim Bi Bj) (F.toPowerSeries m)) (φ i)
      = subst (Sum.elim (atB Bi φ) (atB Bj φ)) (F.toPowerSeries i) := by
  rw [← subst_comp_subst_apply F.hasSubst_toPowerSeries (hasSubst_elim hBi hBj), hφF i,
    subst_subst_pull (hasSubst_elim hBi hBj) hφ]
  rfl

theorem cocycle_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i)) :
    subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
              fun l => X (Sum.inr (Sum.inl l)))
            (F.toPowerSeries j))
          fun j => X (Sum.inr (Sum.inr j)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      + subst
        (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      =
    subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
              fun l => X (Sum.inr (Sum.inr l)))
            (F.toPowerSeries j))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      + subst
        (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ) := by
  have hB12 : HasSubst (Sum.elim (B1 (g := g) (R := R)) B2) := hasSubst_elim cB1 cB2
  have hB23 : HasSubst (Sum.elim (B2 (g := g) (R := R)) B3) := hasSubst_elim cB2 cB3
  have hA : HasSubst (Sum.elim (fun j => subst (Sum.elim (B1 (g := g) (R := R)) B2) (F.toPowerSeries j)) B3) :=
    hasSubst_elim (constantCoeff_subst_elim F cB1 cB2) cB3
  have hA' : HasSubst (Sum.elim B1 fun j => subst (Sum.elim (B2 (g := g) (R := R)) B3) (F.toPowerSeries j)) :=
    hasSubst_elim cB1 (constantCoeff_subst_elim F cB2 cB3)
  show subst (Sum.elim (fun j => subst (Sum.elim B1 B2) (F.toPowerSeries j)) B3) _
      + subst (Sum.elim B1 B2) _
      = subst (Sum.elim B1 fun j => subst (Sum.elim B2 B3) (F.toPowerSeries j)) _ + subst (Sum.elim B2 B3) _
  rw [subst_subst_pull hA hφ, subst_subst_pull hB12 hφ, subst_subst_pull hA' hφ, subst_subst_pull hB23 hφ]
  have k := cocycle_elim F hΓ (constantCoeff_atB cB1 hφ) (constantCoeff_atB cB2 hφ) (constantCoeff_atB cB3 hφ)
  have h1 : (fun i => subst (fun m => Sum.elim (fun j => subst (Sum.elim B1 B2) (F.toPowerSeries j)) B3 (Sum.inl m))
      (φ i)) = fun i => subst (Sum.elim (atB B1 φ) (atB B2 φ)) (F.toPowerSeries i) :=
    funext fun i => subst_lawpair F hφ hφF cB1 cB2 i
  have h2 : (fun i => subst (fun m => Sum.elim B1 (fun j => subst (Sum.elim B2 B3) (F.toPowerSeries j)) (Sum.inr m))
      (φ i)) = fun i => subst (Sum.elim (atB B2 φ) (atB B3 φ)) (F.toPowerSeries i) :=
    funext fun i => subst_lawpair F hφ hφF cB2 cB3 i
  simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢
  rw [h1, h2]
  exact k

end ThreeBlocks

theorem isSymmTwoCocycle_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i)) :
    F.IsSymmTwoCocycle (subst (Sum.elim (inL φ) (inR φ)) Γ) where
  constantCoeff_eq_zero := constantCoeff_subst_elim_cocycle F hΓ (constantCoeff_inL hφ) (constantCoeff_inR hφ)
  symm := symm_pull F hΓ hφ
  cocycle := cocycle_pull F hΓ hφ hφF

theorem pull_addCoboundary (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (g₁ : MvPowerSeries (Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (F.addCoboundary g₁) = F.addCoboundary (subst φ g₁) := by
  have hP : HasSubst (Sum.elim (inL φ) (inR φ)) := hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  rw [addCoboundary, addCoboundary, subst_sub hP, subst_sub hP,
    subst_comp_subst_apply F.hasSubst_toPowerSeries hP, subst_comp_subst_apply hasSubst_XL hP,
    subst_comp_subst_apply hasSubst_XR hP, subst_comp_subst_apply hφs F.hasSubst_toPowerSeries,
    subst_comp_subst_apply hφs hasSubst_XL, subst_comp_subst_apply hφs hasSubst_XR]
  congr 2
  · congr 1; funext i; exact (hφF i).symm
  · congr 1; funext m; exact subst_X hP _
  · congr 1; funext m; exact subst_X hP _

end MvFormalGroup.C1Kit

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow Cob.PA"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] {φ : Fin g → MvPowerSeries (Fin g) R}

theorem hasSubst_pull (hφ : ∀ i, (φ i).constantCoeff = 0) : HasSubst (Sum.elim (inL φ) (inR φ)) :=
  hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)

theorem pull_smul_add (hφ : ∀ i, (φ i).constantCoeff = 0) (c : R) (Γ Γ' : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (c • Γ + Γ')
      = c • subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL φ) (inR φ)) Γ' := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_add, map_smul]

theorem pull_add (hφ : ∀ i, (φ i).constantCoeff = 0) (Γ Γ' : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (Γ + Γ') = subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL φ) (inR φ)) Γ' :=
  subst_add (hasSubst_pull hφ) Γ Γ'

theorem pull_smul (hφ : ∀ i, (φ i).constantCoeff = 0) (c : R) (Γ : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (c • Γ) = c • subst (Sum.elim (inL φ) (inR φ)) Γ := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_smul]

theorem pull_zero (hφ : ∀ i, (φ i).constantCoeff = 0) :
    subst (Sum.elim (inL φ) (inR φ)) (0 : MvPowerSeries (Fin g ⊕ Fin g) R) = 0 := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_zero]

end MvFormalGroup.C1Kit

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow Cob.PA"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R)

theorem addCoboundary_add (g₁ g₂ : MvPowerSeries (Fin g) R) :
    F.addCoboundary (g₁ + g₂) = F.addCoboundary g₁ + F.addCoboundary g₂ := by
  simp only [addCoboundary, subst_add F.hasSubst_toPowerSeries, subst_add hasSubst_XL, subst_add hasSubst_XR]
  ring

theorem addCoboundary_neg (g₁ : MvPowerSeries (Fin g) R) :
    F.addCoboundary (-g₁) = -F.addCoboundary g₁ := by
  simp only [addCoboundary, ← coe_substAlgHom F.hasSubst_toPowerSeries, ← coe_substAlgHom hasSubst_XL,
    ← coe_substAlgHom hasSubst_XR, map_neg]
  ring

end MvFormalGroup.C1Kit

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormalODModule FormalODModule.forall_exists_subst_act_subst_varpi_eq_smul_of_type SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi forall_exists_subst_act_subst_varpi_eq_smul_of_type"
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup.C1Kit CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k]

theorem exists_pull_act_natCast (X₀ : FormalODModule q k) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k)
    (hΓ : X₀.F.IsSymmTwoCocycle Γ) (n : ℕ) :
    ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      subst (Sum.elim (inL (X₀.act (n : Zp2 q))) (inR (X₀.act (n : Zp2 q)))) Γ
        = (n : k) • Γ + X₀.F.addCoboundary g := by
  induction n with
  | zero =>
    obtain ⟨g, hg0, hg⟩ := exists_pull_act_add X₀ 0 0 Γ hΓ
    rw [add_zero] at hg
    refine ⟨-g, by rw [map_neg, hg0, neg_zero], ?_⟩
    rw [Nat.cast_zero, Nat.cast_zero, zero_smul, zero_add, addCoboundary_neg]
    linear_combination -hg
  | succ n ih =>
    obtain ⟨g₁, hg₁0, hg₁⟩ := ih
    obtain ⟨g₂, hg₂0, hg₂⟩ := exists_pull_act_add X₀ (n : Zp2 q) 1 Γ hΓ
    refine ⟨g₁ + g₂, by rw [map_add, hg₁0, hg₂0, add_zero], ?_⟩
    rw [Nat.cast_succ, Nat.cast_succ, hg₂, hg₁, X₀.act_one, addCoboundary_add]
    have h1 : subst (Sum.elim (inL (Series.id k)) (inR (Series.id k))) Γ = Γ := pull_X Γ
    rw [h1, add_smul, one_smul]
    ring

theorem exists_pull_act_char [CharP k q] (X₀ : FormalODModule q k) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k)
    (hΓ : X₀.F.IsSymmTwoCocycle Γ) :
    ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      subst (Sum.elim (inL (X₀.act (q : Zp2 q))) (inR (X₀.act (q : Zp2 q)))) Γ = X₀.F.addCoboundary g := by
  obtain ⟨g, hg0, hg⟩ := exists_pull_act_natCast X₀ Γ hΓ q
  refine ⟨g, hg0, ?_⟩
  rw [hg, CharP.cast_eq_zero, zero_smul, zero_add]

theorem exists_pull_varpi_pull_varpi [CharP k q] (X₀ : FormalODModule q k) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k)
    (hΓ : X₀.F.IsSymmTwoCocycle Γ) :
    ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) (subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) Γ)
        = X₀.F.addCoboundary g := by
  rw [← pull_comp X₀.isLawHom_varpi.1 X₀.isLawHom_varpi.1]
  have h : (fun i => subst X₀.varpi (X₀.varpi i)) = X₀.varpi.comp X₀.varpi := rfl
  rw [h, X₀.varpi_comp_varpi]
  exact exists_pull_act_char X₀ Γ hΓ

theorem exists_pull_act_pull_varpi_of_type (X₀ : FormalODModule q k) (χ : Zp2 q →+* k)
    (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k)
    (hχ : ∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) Γ = χ a • Γ + X₀.F.addCoboundary g) (a : Zp2 q) :
    ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) (subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) Γ)
        = χ (WittVector.frobenius a) • subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) Γ
          + X₀.F.addCoboundary g := by
  obtain ⟨g, hg0, hg⟩ := hχ (WittVector.frobenius a)
  have hv := X₀.isLawHom_varpi
  have ha := X₀.isLawHom_act a
  have hσ := X₀.isLawHom_act (WittVector.frobenius a)
  refine ⟨subst X₀.varpi g, constantCoeff_subst_eq_zero hv.hasSubst hv.1 hg0, ?_⟩
  rw [← pull_comp hv.1 ha.1]
  have h : (fun i => subst (X₀.act a) (X₀.varpi i)) = X₀.varpi.comp (X₀.act a) := rfl
  rw [h, X₀.varpi_comp_act a]
  show subst (Sum.elim (inL fun i => subst X₀.varpi (X₀.act (WittVector.frobenius a) i))
      (inR fun i => subst X₀.varpi (X₀.act (WittVector.frobenius a) i))) Γ = _
  rw [pull_comp hσ.1 hv.1, hg, pull_smul_add hv.1, pull_addCoboundary X₀.F hv.1 hv.2]

end CerednikDrinfeld.FormalODModule

namespace C1cKit

open WittVector

variable (q : ℕ) [hq : Fact q.Prime]

theorem exists_natCast_of_pow_eq {K : Type*} [Field K] [CharP K q] (a : K) (ha : a ^ q = a) :
    ∃ m : ℕ, (m : K) = a := by
  classical

  set P : Polynomial K := Polynomial.X ^ q - Polynomial.X with hP
  have hq1 : 1 < q := hq.out.one_lt
  have hPdeg : P.natDegree = q := by
    rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_X, hq1]
  have hP0 : P ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hPdeg; exact hq.out.ne_zero hPdeg.symm
  have hroot : ∀ b : K, b ^ q = b → b ∈ P.roots := by
    intro b hb
    rw [Polynomial.mem_roots hP0, hP, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hb, sub_self]

  let ι : ZMod q →+* K := ZMod.castHom (dvd_refl q) K
  have hι : Function.Injective ι := ι.injective
  let S : Finset K := Finset.univ.image ι
  have hScard : S.card = q := by
    rw [Finset.card_image_of_injective _ hι, Finset.card_univ, ZMod.card]
  have hSsub : S ⊆ P.roots.toFinset := by
    intro b hb
    rw [Multiset.mem_toFinset]
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hb
    apply hroot
    rw [← map_pow, ZMod.pow_card]
  have hcard : P.roots.toFinset.card ≤ q := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = q := hPdeg
  have hSeq : S = P.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hcard)
  have haS : a ∈ S := by rw [hSeq, Multiset.mem_toFinset]; exact hroot a ha
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp haS
  refine ⟨z.val, ?_⟩
  rw [← hz]
  show ((z.val : ℕ) : K) = (z.cast : K)
  rw [ZMod.cast_eq_val]

theorem frobenius_frobenius (x : CerednikDrinfeld.Zp2 q) :
    frobenius (frobenius x) = x := by
  classical
  haveI := Fintype.ofFinite (GaloisField q 2)
  ext n
  rw [coeff_frobenius_charP, coeff_frobenius_charP, ← pow_mul]
  have hc : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card q 2 two_ne_zero
  have := FiniteField.pow_card (x.coeff n)
  rwa [hc, pow_two] at this

theorem exists_eq_natCast_add_mul_of_frobenius_eq (x : CerednikDrinfeld.Zp2 q) (hx : frobenius x = x) :
    ∃ (m : ℕ) (c : CerednikDrinfeld.Zp2 q), x = m + (q : CerednikDrinfeld.Zp2 q) * c := by
  have h0 : (x.coeff 0) ^ q = x.coeff 0 := by
    have := congrArg (fun y => WittVector.coeff y 0) hx
    simpa only [coeff_frobenius_charP] using this
  obtain ⟨m, hm⟩ := exists_natCast_of_pow_eq q (x.coeff 0) h0
  have hy : (x - m) ∈ Ideal.span {(q : CerednikDrinfeld.Zp2 q)} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero, ← constantCoeff_apply, map_sub, map_natCast, constantCoeff_apply,
      ← hm, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy
  exact ⟨m, c, by rw [mul_comm, hc]; ring⟩

theorem exists_pow_ne : ∃ ζ : GaloisField q 2, ζ ^ q ≠ ζ := by
  classical
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun m : ZMod q => (m.cast : GaloisField q 2)) := by
    intro a
    obtain ⟨m, hm⟩ := exists_natCast_of_pow_eq q a (h a)
    exact ⟨(m : ZMod q), by show ((m : ZMod q).cast : GaloisField q 2) = a; rw [ZMod.cast_natCast (dvd_refl q), hm]⟩
  haveI := Fintype.ofFinite (GaloisField q 2)
  have hle : Fintype.card (GaloisField q 2) ≤ Fintype.card (ZMod q) := Fintype.card_le_of_surjective _ hsurj
  rw [ZMod.card, ← Nat.card_eq_fintype_card, GaloisField.card q 2 two_ne_zero, pow_two] at hle
  have hq1 : 1 < q := hq.out.one_lt
  nlinarith

theorem exists_isUnit_sub_frobenius :
    ∃ z : CerednikDrinfeld.Zp2 q, IsUnit (z - frobenius z) := by
  obtain ⟨ζ, hζ⟩ := exists_pow_ne q
  refine ⟨teichmuller q ζ, isUnit_of_coeff_zero_ne_zero _ ?_⟩
  rw [← constantCoeff_apply, map_sub, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero,
    coeff_frobenius_charP, teichmuller_coeff_zero]
  exact sub_ne_zero.mpr (Ne.symm hζ)

end C1cKit

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow Cob.PA"
p2m_open "MvFormalGroup"

namespace C1Kit

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R)

theorem addCoboundary_zero : F.addCoboundary 0 = 0 := by
  rw [addCoboundary, ← coe_substAlgHom F.hasSubst_toPowerSeries, ← coe_substAlgHom hasSubst_XL,
    ← coe_substAlgHom hasSubst_XR, map_zero, map_zero, map_zero, sub_zero, sub_zero]

theorem addCoboundary_smul (c : R) (h : MvPowerSeries (Fin g) R) :
    F.addCoboundary (c • h) = c • F.addCoboundary h := by
  rw [addCoboundary, addCoboundary, subst_smul F.hasSubst_toPowerSeries, subst_smul hasSubst_XL,
    subst_smul hasSubst_XR, smul_sub, smul_sub]

end C1Kit

variable {g : ℕ} {R : Type*} [CommRing R]

private def _root_.MvFormalGroup.Cob (F : MvFormalGroup g R) (Γ Γ' : MvPowerSeries (Fin g ⊕ Fin g) R) : Prop :=
  ∃ h : MvPowerSeries (Fin g) R, h.constantCoeff = 0 ∧ Γ = Γ' + F.addCoboundary h

p2m_export "MvFormalGroup" "Cob"
namespace Cob

open MvFormalGroup.C1Kit

variable {F : MvFormalGroup g R}
variable {Γ Γ' Γ'' Δ Δ' : MvPowerSeries (Fin g ⊕ Fin g) R}

private theorem _root_.MvFormalGroup.Cob.of_eq (h : Γ = Γ') : F.Cob Γ Γ' := ⟨0, map_zero _, by rw [addCoboundary_zero, add_zero]; exact h⟩

p2m_export "MvFormalGroup.Cob" "of_eq"
private theorem _root_.MvFormalGroup.Cob.rfl' : F.Cob Γ Γ := of_eq rfl

p2m_export "MvFormalGroup.Cob" "rfl'"
private theorem _root_.MvFormalGroup.Cob.trans (h₁ : F.Cob Γ Γ') (h₂ : F.Cob Γ' Γ'') : F.Cob Γ Γ'' := by
  obtain ⟨a, ha, ea⟩ := h₁
  obtain ⟨b, hb, eb⟩ := h₂
  refine ⟨b + a, by rw [map_add, ha, hb, add_zero], ?_⟩
  rw [addCoboundary_add, ea, eb, add_assoc]

p2m_export "MvFormalGroup.Cob" "trans"
private theorem _root_.MvFormalGroup.Cob.symm (h₁ : F.Cob Γ Γ') : F.Cob Γ' Γ := by
  obtain ⟨a, ha, ea⟩ := h₁
  refine ⟨-a, by rw [map_neg, ha, neg_zero], ?_⟩
  rw [addCoboundary_neg, ea]; ring

p2m_export "MvFormalGroup.Cob" "symm"
private theorem _root_.MvFormalGroup.Cob.add (h₁ : F.Cob Γ Γ') (h₂ : F.Cob Δ Δ') : F.Cob (Γ + Δ) (Γ' + Δ') := by
  obtain ⟨a, ha, ea⟩ := h₁
  obtain ⟨b, hb, eb⟩ := h₂
  refine ⟨a + b, by rw [map_add, ha, hb, add_zero], ?_⟩
  rw [addCoboundary_add, ea, eb]; ring

p2m_export "MvFormalGroup.Cob" "add"
private theorem _root_.MvFormalGroup.Cob.smul (c : R) (h₁ : F.Cob Γ Γ') : F.Cob (c • Γ) (c • Γ') := by
  obtain ⟨a, ha, ea⟩ := h₁
  refine ⟨c • a, by rw [MvPowerSeries.constantCoeff_smul, ha, smul_zero], ?_⟩
  rw [addCoboundary_smul, ea, smul_add]

p2m_export "MvFormalGroup.Cob" "smul"
private theorem _root_.MvFormalGroup.Cob.pull {φ : Fin g → MvPowerSeries (Fin g) R} (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (h₁ : F.Cob Γ Γ') :
    F.Cob (subst (Sum.elim (inL φ) (inR φ)) Γ) (subst (Sum.elim (inL φ) (inR φ)) Γ') := by
  obtain ⟨a, ha, ea⟩ := h₁
  refine ⟨subst φ a, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hφ) hφ ha, ?_⟩
  rw [ea, pull_add hφ, pull_addCoboundary F hφ hφF]

p2m_export "MvFormalGroup.Cob" "pull"
end Cob

namespace C1Kit

variable (F : MvFormalGroup g R)

theorem IsSymmTwoCocycle.add' {Γ Γ' : MvPowerSeries (Fin g ⊕ Fin g) R} (hΓ : F.IsSymmTwoCocycle Γ)
    (hΓ' : F.IsSymmTwoCocycle Γ') : F.IsSymmTwoCocycle (Γ + Γ') where
  constantCoeff_eq_zero := by rw [map_add, hΓ.constantCoeff_eq_zero, hΓ'.constantCoeff_eq_zero, add_zero]
  symm := by
    have hswap : HasSubst (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) fun j => X (Sum.inl j)) :=
      hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
    rw [subst_add hswap, hΓ.symm, hΓ'.symm]
  cocycle := by
    have hB12 : HasSubst (Sum.elim (B1 (g := g) (R := R)) B2) := hasSubst_elim cB1 cB2
    have hB23 : HasSubst (Sum.elim (B2 (g := g) (R := R)) B3) := hasSubst_elim cB2 cB3
    have hA : HasSubst (Sum.elim (fun j => subst (Sum.elim (B1 (g := g) (R := R)) B2) (F.toPowerSeries j)) B3) :=
      hasSubst_elim (constantCoeff_subst_elim F cB1 cB2) cB3
    have hA' : HasSubst (Sum.elim B1 fun j => subst (Sum.elim (B2 (g := g) (R := R)) B3) (F.toPowerSeries j)) :=
      hasSubst_elim cB1 (constantCoeff_subst_elim F cB2 cB3)
    show subst (Sum.elim (fun j => subst (Sum.elim B1 B2) (F.toPowerSeries j)) B3) _
        + subst (Sum.elim B1 B2) _
        = subst (Sum.elim B1 fun j => subst (Sum.elim B2 B3) (F.toPowerSeries j)) _ + subst (Sum.elim B2 B3) _
    rw [subst_add hA, subst_add hB12, subst_add hA', subst_add hB23]
    have h1 := hΓ.cocycle
    have h2 := hΓ'.cocycle
    linear_combination h1 + h2

theorem IsSymmTwoCocycle.smul' (c : R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R} (hΓ : F.IsSymmTwoCocycle Γ) :
    F.IsSymmTwoCocycle (c • Γ) where
  constantCoeff_eq_zero := by rw [MvPowerSeries.constantCoeff_smul, hΓ.constantCoeff_eq_zero, smul_zero]
  symm := by
    have hswap : HasSubst (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) fun j => X (Sum.inl j)) :=
      hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
    rw [subst_smul hswap, hΓ.symm]
  cocycle := by
    have hB12 : HasSubst (Sum.elim (B1 (g := g) (R := R)) B2) := hasSubst_elim cB1 cB2
    have hB23 : HasSubst (Sum.elim (B2 (g := g) (R := R)) B3) := hasSubst_elim cB2 cB3
    have hA : HasSubst (Sum.elim (fun j => subst (Sum.elim (B1 (g := g) (R := R)) B2) (F.toPowerSeries j)) B3) :=
      hasSubst_elim (constantCoeff_subst_elim F cB1 cB2) cB3
    have hA' : HasSubst (Sum.elim B1 fun j => subst (Sum.elim (B2 (g := g) (R := R)) B3) (F.toPowerSeries j)) :=
      hasSubst_elim cB1 (constantCoeff_subst_elim F cB2 cB3)
    show subst (Sum.elim (fun j => subst (Sum.elim B1 B2) (F.toPowerSeries j)) B3) _
        + subst (Sum.elim B1 B2) _
        = subst (Sum.elim B1 fun j => subst (Sum.elim B2 B3) (F.toPowerSeries j)) _ + subst (Sum.elim B2 B3) _
    rw [subst_smul hA, subst_smul hB12, subst_smul hA', subst_smul hB23, ← smul_add, ← smul_add, hΓ.cocycle]

end C1Kit

end MvFormalGroup

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormalODModule FormalODModule.forall_exists_subst_act_subst_varpi_eq_smul_of_type SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi forall_exists_subst_act_subst_varpi_eq_smul_of_type"
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup.C1Kit CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k]

private noncomputable abbrev _root_.CerednikDrinfeld.FormalODModule.PA (X₀ : FormalODModule q k) (a : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) :
    MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) Γ

p2m_export "CerednikDrinfeld.FormalODModule" "PA"
variable (X₀ : FormalODModule q k)

theorem PA_mul (a b : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) :
    X₀.PA (a * b) Γ = X₀.PA b (X₀.PA a Γ) := by
  show subst (Sum.elim (inL (X₀.act (a * b))) (inR (X₀.act (a * b)))) Γ = _
  rw [X₀.act_mul]
  exact pull_comp (X₀.isLawHom_act a).1 (X₀.isLawHom_act b).1 Γ

theorem cob_PA_add {Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (hΓ : X₀.F.IsSymmTwoCocycle Γ) (a b : Zp2 q) :
    X₀.F.Cob (X₀.PA (a + b) Γ) (X₀.PA a Γ + X₀.PA b Γ) :=
  exists_pull_act_add X₀ a b Γ hΓ

theorem cob_PA_natCast {Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (hΓ : X₀.F.IsSymmTwoCocycle Γ) (n : ℕ) :
    X₀.F.Cob (X₀.PA (n : Zp2 q) Γ) ((n : k) • Γ) :=
  exists_pull_act_natCast X₀ Γ hΓ n

theorem cob_PA_char [CharP k q] {Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (hΓ : X₀.F.IsSymmTwoCocycle Γ) :
    X₀.F.Cob (X₀.PA (q : Zp2 q) Γ) 0 := by
  obtain ⟨h, hh, e⟩ := exists_pull_act_char X₀ Γ hΓ
  exact ⟨h, hh, by rw [zero_add]; exact e⟩

private theorem _root_.MvFormalGroup.Cob.PA {Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (a : Zp2 q) (h : X₀.F.Cob Γ Γ') :
    X₀.F.Cob (X₀.PA a Γ) (X₀.PA a Γ') :=
  h.pull (X₀.isLawHom_act a).1 (X₀.isLawHom_act a).2

p2m_alias "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup.Cob.PA" "MvFormalGroup.Cob.PA"
theorem isSymmTwoCocycle_PA {Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (hΓ : X₀.F.IsSymmTwoCocycle Γ) (a : Zp2 q) :
    X₀.F.IsSymmTwoCocycle (X₀.PA a Γ) :=
  isSymmTwoCocycle_pull X₀.F hΓ (X₀.isLawHom_act a).1 (X₀.isLawHom_act a).2

theorem PA_zero' (a : Zp2 q) : X₀.PA a 0 = 0 := pull_zero (X₀.isLawHom_act a).1

theorem PA_smul (a : Zp2 q) (c : k) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) : X₀.PA a (c • Γ) = c • X₀.PA a Γ :=
  pull_smul (X₀.isLawHom_act a).1 c Γ

theorem PA_add (a : Zp2 q) (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k) : X₀.PA a (Γ + Γ') = X₀.PA a Γ + X₀.PA a Γ' :=
  pull_add (X₀.isLawHom_act a).1 Γ Γ'

theorem cob_PA_of_frobenius_eq [CharP k q] (j₀ : Zp2 q →+* k) {Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k}
    (hΓ : X₀.F.IsSymmTwoCocycle Γ) {x : Zp2 q} (hx : WittVector.frobenius x = x) :
    X₀.F.Cob (X₀.PA x Γ) (j₀ x • Γ) := by
  obtain ⟨m, c, hxe⟩ := C1cKit.exists_eq_natCast_add_mul_of_frobenius_eq q x hx
  have hj : j₀ x = (m : k) := by
    rw [hxe, map_add, map_natCast, map_mul, map_natCast, CharP.cast_eq_zero k q, zero_mul, add_zero]
  rw [hj, hxe]
  refine (cob_PA_add X₀ hΓ _ _).trans ?_
  have h1 : X₀.F.Cob (X₀.PA (m : Zp2 q) Γ) ((m : k) • Γ) := cob_PA_natCast X₀ hΓ m
  have h2 : X₀.F.Cob (X₀.PA ((q : Zp2 q) * c) Γ) 0 := by
    rw [PA_mul]
    have := (cob_PA_char X₀ hΓ).PA X₀ c
    rwa [PA_zero'] at this
  have := h1.add h2
  rwa [add_zero] at this

theorem exists_decomp (z : Zp2 q) (hz : IsUnit (z - WittVector.frobenius z)) (a : Zp2 q) :
    ∃ c₀ c₁ : Zp2 q, WittVector.frobenius c₀ = c₀ ∧ WittVector.frobenius c₁ = c₁ ∧ a = c₀ + c₁ * z := by
  obtain ⟨d, hd⟩ := hz
  set σ := (WittVector.frobenius : Zp2 q →+* Zp2 q) with hσ
  have hσσ : ∀ y : Zp2 q, σ (σ y) = y := C1cKit.frobenius_frobenius q
  have hσd : σ (d : Zp2 q) = -(d : Zp2 q) := by rw [hd, map_sub, hσσ]; ring
  have hσdi : σ (↑d⁻¹ : Zp2 q) = -(↑d⁻¹ : Zp2 q) := by
    have h1 : σ (↑d⁻¹ : Zp2 q) * σ (d : Zp2 q) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    rw [hσd] at h1
    calc σ (↑d⁻¹ : Zp2 q) = σ (↑d⁻¹ : Zp2 q) * (-(d : Zp2 q)) * (-(↑d⁻¹ : Zp2 q)) := by
          rw [mul_assoc, neg_mul_neg, Units.mul_inv, mul_one]
      _ = -(↑d⁻¹ : Zp2 q) := by rw [h1, one_mul]
  refine ⟨(z * σ a - a * σ z) * ↑d⁻¹, (a - σ a) * ↑d⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_sub, map_mul, map_mul, hσσ, hσσ, hσdi]; ring
  · rw [map_mul, map_sub, hσσ, hσdi]; ring
  · have hdd : (z - σ z) * ↑d⁻¹ = 1 := by rw [← hd, Units.mul_inv]
    linear_combination (-a) * hdd

theorem cob_eigen {Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (z : Zp2 q) (α β e : k)
    (hT : X₀.F.Cob (X₀.PA z (X₀.PA z Γ)) ((α + β) • X₀.PA z Γ + (-(α * β)) • Γ)) :
    X₀.F.Cob (X₀.PA z (e • X₀.PA z Γ + (-(β * e)) • Γ)) (α • (e • X₀.PA z Γ + (-(β * e)) • Γ)) := by
  rw [PA_add, PA_smul, PA_smul]
  have h := (hT.smul e).add (Cob.rfl' (F := X₀.F) (Γ := (-(β * e)) • X₀.PA z Γ))
  refine h.trans (Cob.of_eq ?_)
  module

theorem exists_split [CharP k q] (j₀ : Zp2 q →+* k) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k)
    (hΓ : X₀.F.IsSymmTwoCocycle Γ) :
    ∃ (Γ₀ Γ₁ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (g : MvPowerSeries (Fin 2) k),
      X₀.F.IsSymmTwoCocycle Γ₀ ∧ X₀.F.IsSymmTwoCocycle Γ₁ ∧
      (∀ a : Zp2 q, ∃ g₀ : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g₀ = 0 ∧
          X₀.PA a Γ₀ = j₀ a • Γ₀ + X₀.F.addCoboundary g₀) ∧
      (∀ a : Zp2 q, ∃ g₁ : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g₁ = 0 ∧
          X₀.PA a Γ₁ = j₀ (WittVector.frobenius a) • Γ₁ + X₀.F.addCoboundary g₁) ∧
      MvPowerSeries.constantCoeff g = 0 ∧
      Γ = Γ₀ + Γ₁ + X₀.F.addCoboundary g := by
  obtain ⟨z, hz⟩ := C1cKit.exists_isUnit_sub_frobenius q
  set σ := (WittVector.frobenius : Zp2 q →+* Zp2 q) with hσ
  have hσσ : ∀ y : Zp2 q, σ (σ y) = y := C1cKit.frobenius_frobenius q
  set α : k := j₀ z with hα
  set β : k := j₀ (σ z) with hβ

  have hαβ : α - β ≠ 0 := by
    rw [hα, hβ, ← map_sub]
    exact (hz.map j₀).ne_zero
  set e : k := (α - β)⁻¹ with he
  have hee : (α - β) * e = 1 := mul_inv_cancel₀ hαβ

  set T := X₀.PA z with hTdef
  have hs : σ (z + σ z) = z + σ z := by rw [map_add, hσσ, add_comm]
  have ht : σ (z * σ z) = z * σ z := by rw [map_mul, hσσ, mul_comm]
  have hzz : z * z + z * σ z = (z + σ z) * z := by ring
  have hquad : ∀ {Δ : MvPowerSeries (Fin 2 ⊕ Fin 2) k}, X₀.F.IsSymmTwoCocycle Δ →
      X₀.F.Cob (T (T Δ)) ((α + β) • T Δ + (-(α * β)) • Δ) := by
    intro Δ hΔ

    have l1 : X₀.F.Cob (X₀.PA (z * z + z * σ z) Δ) (T (T Δ) + (α * β) • Δ) := by
      refine (cob_PA_add X₀ hΔ _ _).trans ?_
      rw [PA_mul]
      refine (Cob.rfl'.add (cob_PA_of_frobenius_eq X₀ j₀ hΔ ht)).trans (Cob.of_eq ?_)
      rw [map_mul, ← hα, ← hβ]
    have l2 : X₀.F.Cob (X₀.PA ((z + σ z) * z) Δ) ((α + β) • T Δ) := by
      rw [PA_mul]
      refine ((cob_PA_of_frobenius_eq X₀ j₀ hΔ hs).PA X₀ z).trans (Cob.of_eq ?_)
      rw [PA_smul, map_add, ← hα, ← hβ]
    rw [hzz] at l1
    have l3 := (l1.symm.trans l2)

    have l4 := l3.add (Cob.rfl' (F := X₀.F) (Γ := (-(α * β)) • Δ))
    refine (Cob.of_eq ?_).trans l4
    module

  set Γ₀ : MvPowerSeries (Fin 2 ⊕ Fin 2) k := e • T Γ + (-(β * e)) • Γ with hΓ₀
  set Γ₁ : MvPowerSeries (Fin 2 ⊕ Fin 2) k := (-e) • T Γ + (α * e) • Γ with hΓ₁
  have hTΓ : X₀.F.IsSymmTwoCocycle (T Γ) := isSymmTwoCocycle_PA X₀ hΓ z
  have hΓ₀c : X₀.F.IsSymmTwoCocycle Γ₀ :=
    IsSymmTwoCocycle.add' X₀.F (IsSymmTwoCocycle.smul' X₀.F e hTΓ) (IsSymmTwoCocycle.smul' X₀.F _ hΓ)
  have hΓ₁c : X₀.F.IsSymmTwoCocycle Γ₁ :=
    IsSymmTwoCocycle.add' X₀.F (IsSymmTwoCocycle.smul' X₀.F _ hTΓ) (IsSymmTwoCocycle.smul' X₀.F _ hΓ)

  have hE₀ : X₀.F.Cob (T Γ₀) (α • Γ₀) := cob_eigen X₀ z α β e (hquad hΓ)
  have hE₁ : X₀.F.Cob (T Γ₁) (β • Γ₁) := by
    have hq' : X₀.F.Cob (X₀.PA z (X₀.PA z Γ)) ((β + α) • X₀.PA z Γ + (-(β * α)) • Γ) := by
      rw [add_comm β α, mul_comm β α]; exact hquad hΓ
    have := cob_eigen X₀ z β α (-e) hq'
    have h1 : -(α * -e) = α * e := by ring
    rwa [h1] at this

  have key : ∀ (Δ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (γ : k), X₀.F.IsSymmTwoCocycle Δ → X₀.F.Cob (T Δ) (γ • Δ) →
      ∀ a : Zp2 q, ∀ c₀ c₁ : Zp2 q, σ c₀ = c₀ → σ c₁ = c₁ → a = c₀ + c₁ * z →
        X₀.F.Cob (X₀.PA a Δ) ((j₀ c₀ + j₀ c₁ * γ) • Δ) := by
    intro Δ γ hΔ hTΔ a c₀ c₁ hc₀ hc₁ hae
    rw [hae]
    refine (cob_PA_add X₀ hΔ _ _).trans ?_
    rw [PA_mul]
    have h0 := cob_PA_of_frobenius_eq X₀ j₀ hΔ hc₀
    have h1 : X₀.F.Cob (X₀.PA z (X₀.PA c₁ Δ)) ((j₀ c₁ * γ) • Δ) := by
      refine ((cob_PA_of_frobenius_eq X₀ j₀ hΔ hc₁).PA X₀ z).trans ?_
      rw [PA_smul, mul_smul]
      exact hTΔ.smul _
    exact (h0.add h1).trans (Cob.of_eq (by rw [add_smul]))
  refine ⟨Γ₀, Γ₁, 0, hΓ₀c, hΓ₁c, ?_, ?_, map_zero _, ?_⟩
  · intro a
    obtain ⟨c₀, c₁, hc₀, hc₁, hae⟩ := exists_decomp z hz a
    have hj : j₀ a = j₀ c₀ + j₀ c₁ * α := by rw [hae, map_add, map_mul, hα]
    rw [hj]
    exact key Γ₀ α hΓ₀c hE₀ a c₀ c₁ hc₀ hc₁ hae
  · intro a
    obtain ⟨c₀, c₁, hc₀, hc₁, hae⟩ := exists_decomp z hz a
    have hj : j₀ (WittVector.frobenius a) = j₀ c₀ + j₀ c₁ * β := by
      rw [hae, map_add, map_mul, map_add, map_mul, hβ]
      show j₀ (σ c₀) + j₀ (σ c₁) * j₀ (σ z) = _
      rw [hc₀, hc₁]
    rw [hj]
    exact key Γ₁ β hΓ₁c hE₁ a c₀ c₁ hc₀ hc₁ hae
  · rw [addCoboundary_zero, add_zero, hΓ₀, hΓ₁]
    have hsum : (e • T Γ + (-(β * e)) • Γ) + ((-e) • T Γ + (α * e) • Γ) = ((α - β) * e) • Γ := by module
    rw [hsum, hee, one_smul]

end CerednikDrinfeld.FormalODModule

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow Cob.PA"
namespace C1Kit
p2m_open "MvFormalGroup"
variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R)
theorem addCoboundary_sub' (g₁ g₂ : MvPowerSeries (Fin g) R) :
    F.addCoboundary (g₁ - g₂) = F.addCoboundary g₁ - F.addCoboundary g₂ := by
  rw [sub_eq_add_neg, addCoboundary_add, addCoboundary_neg, ← sub_eq_add_neg]
end MvFormalGroup.C1Kit

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormalODModule FormalODModule.forall_exists_subst_act_subst_varpi_eq_smul_of_type SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi forall_exists_subst_act_subst_varpi_eq_smul_of_type"
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup.C1Kit CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] (X₀ : FormalODModule q k)

theorem cob_type_lincomb (χ : Zp2 q → k) {Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k}
    (hΓ : ∀ a, X₀.F.Cob (X₀.PA a Γ) (χ a • Γ)) (hΓ' : ∀ a, X₀.F.Cob (X₀.PA a Γ') (χ a • Γ'))
    (u u' : k) (a : Zp2 q) :
    X₀.F.Cob (X₀.PA a (u • Γ + u' • Γ')) (χ a • (u • Γ + u' • Γ')) := by
  rw [PA_add, PA_smul, PA_smul]
  refine (((hΓ a).smul u).add ((hΓ' a).smul u')).trans (Cob.of_eq ?_)
  module

theorem cob_type_of_cob (χ : Zp2 q → k) {Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k} (h : X₀.F.Cob Γ Γ')
    (hΓ' : ∀ a, X₀.F.Cob (X₀.PA a Γ') (χ a • Γ')) (a : Zp2 q) :
    X₀.F.Cob (X₀.PA a Γ) (χ a • Γ) :=
  ((h.PA X₀ a).trans (hΓ' a)).trans (h.smul _).symm

theorem cob_zero_of_two_types (χ χ' : Zp2 q → k) {Δ : MvPowerSeries (Fin 2 ⊕ Fin 2) k}
    (h₁ : ∀ a, X₀.F.Cob (X₀.PA a Δ) (χ a • Δ)) (h₂ : ∀ a, X₀.F.Cob (X₀.PA a Δ) (χ' a • Δ))
    {a₀ : Zp2 q} (ha : χ a₀ ≠ χ' a₀) : X₀.F.Cob Δ 0 := by
  have h : X₀.F.Cob ((χ a₀ - χ' a₀) • Δ) 0 := by
    have := (h₁ a₀).symm.trans (h₂ a₀)
    have h' := this.add (Cob.rfl' (F := X₀.F) (Γ := -(χ' a₀ • Δ)))
    refine (Cob.of_eq ?_).trans (h'.trans (Cob.of_eq ?_)) <;> module
  have h' := h.smul (χ a₀ - χ' a₀)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr ha), one_smul, smul_zero] at h'

end CerednikDrinfeld.FormalODModule

open MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.MvFormalGroup MvFormalGroup.C1Kit in
open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.CerednikDrinfeld CerednikDrinfeld.SpecialFormal _root_.CerednikDrinfeld.FormalODModule _root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add.CerednikDrinfeld.FormalODModule in

theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) (χ : Zp2 q →+* k) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    ∀ (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      X₀.F.IsSymmTwoCocycle Γ → X₀.F.IsSymmTwoCocycle Γ' →
      (∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
          pull (X₀.act a) Γ = χ a • Γ + X₀.F.addCoboundary g) →
      (∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
          pull (X₀.act a) Γ' = χ a • Γ' + X₀.F.addCoboundary g) →
      ∃ (c c' : k) (g : MvPowerSeries (Fin 2) k), (c ≠ 0 ∨ c' ≠ 0) ∧ MvPowerSeries.constantCoeff g = 0 ∧
        c • Γ + c' • Γ' = X₀.F.addCoboundary g := by
  intro pull Γ Γ' hΓ hΓ' hT hT'
  classical
  haveI := X₀.isComm
  set X := X₀.toFormalODModule with hXdef

  have hh : Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X₀.F.nthSeries q))) = q ^ 4 := by
    obtain ⟨-, -, hdeg⟩ := X₀.hasHeight
    have h1 := hdeg k (RingHom.id k)
    have e : (X₀.act (q : Zp2 q)).map (RingHom.id k) = X₀.F.nthSeries q := by
      rw [← X₀.act_natCast]; funext i; simp [Series.map]
    rw [e] at h1
    exact h1
  obtain ⟨r, B, hr, hB, hspan⟩ :=
    MvFormalGroup.exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow q X₀.F 4 hh
  obtain ⟨a, g, hg0, hΓe⟩ := hspan Γ hΓ
  obtain ⟨a', g', hg0', hΓ'e⟩ := hspan Γ' hΓ'

  have hTc : ∀ b, X.F.Cob (X.PA b Γ) (χ b • Γ) := fun b => hT b
  have hTc' : ∀ b, X.F.Cob (X.PA b Γ') (χ b • Γ') := fun b => hT' b
  by_cases hdep : ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • a + c' • a' = 0
  ·
    obtain ⟨c, c', hcc, hlin⟩ := hdep
    refine ⟨c, c', c • g + c' • g', hcc, by
      rw [map_add, MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_smul, hg0, hg0', smul_zero,
        smul_zero, add_zero], ?_⟩
    have hsum : ∑ j, (c * a j + c' * a' j) • B j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congr_fun hlin j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [this, zero_smul]
    rw [hΓe, hΓ'e, addCoboundary_add, addCoboundary_smul, addCoboundary_smul, smul_add, smul_add, Finset.smul_sum,
      Finset.smul_sum]
    simp_rw [smul_smul]
    rw [show ∑ j, (c * a j) • B j + c • X₀.F.addCoboundary g + (∑ j, (c' * a' j) • B j + c' • X₀.F.addCoboundary g')
        = ∑ j, (c * a j + c' * a' j) • B j + (c • X₀.F.addCoboundary g + c' • X₀.F.addCoboundary g') by
      rw [Finset.sum_congr rfl fun j _ => add_smul (c * a j) (c' * a' j) (B j), Finset.sum_add_distrib]; abel,
      hsum, zero_add]
  ·
    push Not at hdep
    have hli : LinearIndependent k ![a, a'] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_contra hne
      exact hdep s t (by tauto) hst
    have hr2 : r = 2 := by
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_fin, Module.finrank_fin_fun] at this
      omega
    have htop : Submodule.span k (Set.range ![a, a']) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simp [hr2])
    have hcoord : ∀ e : Fin r → k, ∃ u u' : k, e = u • a + u' • a' := by
      intro e
      have he : e ∈ Submodule.span k (Set.range ![a, a']) := by rw [htop]; exact Submodule.mem_top
      obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp he
      refine ⟨w 0, w 1, ?_⟩
      rw [← hw, Fin.sum_univ_two]
      rfl

    obtain ⟨z, hz⟩ := C1cKit.exists_isUnit_sub_frobenius q
    have hχz : χ z ≠ χ (WittVector.frobenius z) := by
      intro h
      apply (hz.map χ).ne_zero
      rw [map_sub, h, sub_self]

    have hker : ∀ {Δ : MvPowerSeries (Fin 2 ⊕ Fin 2) k}, X₀.F.IsSymmTwoCocycle Δ →
        (∀ b, X.F.Cob (X.PA b Δ) (χ b • Δ)) →
        ∃ gΔ : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff gΔ = 0 ∧
          pull X₀.varpi Δ = X₀.F.addCoboundary gΔ := by
      intro Δ hΔ hTΔ

      have hPD : X₀.F.IsSymmTwoCocycle (pull X₀.varpi Δ) :=
        isSymmTwoCocycle_pull X₀.F hΔ X₀.isLawHom_varpi.1 X₀.isLawHom_varpi.2
      obtain ⟨e, gΔ, hgΔ, hΔe⟩ := hspan _ hPD
      obtain ⟨u, u', hue⟩ := hcoord e
      have hcomb : X.F.Cob (pull X₀.varpi Δ) (u • Γ + u' • Γ') := by
        refine ⟨gΔ - u • g - u' • g', by
          rw [map_sub, map_sub, MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_smul, hgΔ, hg0,
            hg0', smul_zero, smul_zero, sub_zero, sub_zero], ?_⟩
        rw [hΔe, hue]
        have e1 : Γ - X₀.F.addCoboundary g = ∑ j, a j • B j := by rw [hΓe]; abel
        have e2 : Γ' - X₀.F.addCoboundary g' = ∑ j, a' j • B j := by rw [hΓ'e]; abel
        rw [show ∑ j, (u • a + u' • a') j • B j = u • ∑ j, a j • B j + u' • ∑ j, a' j • B j by
          rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, smul_smul],
          ← e1, ← e2, addCoboundary_sub' X₀.F, addCoboundary_sub' X₀.F, addCoboundary_smul, addCoboundary_smul]
        module
      have hT1 : ∀ b, X.F.Cob (X.PA b (pull X₀.varpi Δ)) (χ b • pull X₀.varpi Δ) := fun b =>
        cob_type_of_cob X χ hcomb (cob_type_lincomb X χ hTc hTc' u u') b
      have hT2 : ∀ b, X.F.Cob (X.PA b (pull X₀.varpi Δ)) ((χ ∘ WittVector.frobenius) b • pull X₀.varpi Δ) :=
        fun b => CerednikDrinfeld.FormalODModule.forall_exists_subst_act_subst_varpi_eq_smul_of_type X₀ χ Δ hΔ
          (fun b' => hTΔ b') b
      obtain ⟨h0, hh0, eh⟩ := cob_zero_of_two_types X χ (χ ∘ WittVector.frobenius) hT1 hT2 hχz
      exact ⟨h0, hh0, by rw [eh, zero_add]⟩
    exact CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary
      X₀ χ Γ Γ' hΓ hΓ' hT hT' (hker hΓ hTc) (hker hΓ' hTc')

end S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_forall_subst_act_eq_smul_add (solution)
