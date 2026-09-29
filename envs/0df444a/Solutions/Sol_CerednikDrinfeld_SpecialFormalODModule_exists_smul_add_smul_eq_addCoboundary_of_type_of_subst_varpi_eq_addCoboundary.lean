-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/92820975-6571-5483-a0a4-63f320e13a2c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow
import Theorems.Thm_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "coeff_single_subst hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries linearPart toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle map_ringHom_id eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span Cob.PA"
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
p2m_export "MvFormalGroup" "coeff_single_subst hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries linearPart toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle map_ringHom_id eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span Cob.PA"
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

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Zp2 FormalODModule FormalODModule.act_natCast SpecialFormalODModule SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero" namespace FormalODModule p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast Lie lieAct lieZero lieOne varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi isSymmTwoCocycle_subst_act_and_subst_act_add" end CerednikDrinfeld.FormalODModule
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalODModule" in
open MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.MvFormalGroup MvFormalGroup.C1Kit _root_.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

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
p2m_export "MvFormalGroup" "coeff_single_subst hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries linearPart toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle map_ringHom_id eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span Cob.PA"
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
p2m_export "MvFormalGroup" "coeff_single_subst hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries linearPart toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle map_ringHom_id eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span Cob.PA"
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
p2m_export "MvFormalGroup" "coeff_single_subst hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries linearPart toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle map_ringHom_id eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span Cob.PA"
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
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule FormalODModule.act_natCast SpecialFormalODModule SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast Lie lieAct lieZero lieOne varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi isSymmTwoCocycle_subst_act_and_subst_act_add"
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.MvFormalGroup.C1Kit CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

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
p2m_export "MvFormalGroup" "coeff_single_subst hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries linearPart toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle map_ringHom_id eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span Cob.PA"
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
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule FormalODModule.act_natCast SpecialFormalODModule SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast Lie lieAct lieZero lieOne varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi isSymmTwoCocycle_subst_act_and_subst_act_add"
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.MvFormalGroup.C1Kit CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

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

p2m_alias "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.MvFormalGroup.Cob.PA" "MvFormalGroup.Cob.PA"
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
p2m_export "MvFormalGroup" "coeff_single_subst hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries linearPart toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle map_ringHom_id eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span Cob.PA"
namespace C1Kit
p2m_open "MvFormalGroup"
variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R)
theorem addCoboundary_sub' (g₁ g₂ : MvPowerSeries (Fin g) R) :
    F.addCoboundary (g₁ - g₂) = F.addCoboundary g₁ - F.addCoboundary g₂ := by
  rw [sub_eq_add_neg, addCoboundary_add, addCoboundary_neg, ← sub_eq_add_neg]
end MvFormalGroup.C1Kit

namespace MvFormalGroup
p2m_export "MvFormalGroup" "coeff_single_subst hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries map nthSeries linearPart toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle map_ringHom_id eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span Cob.PA"
namespace C1Kit
p2m_open "MvFormalGroup"
section Peel

variable {σ R : Type*} [CommRing R]

theorem mem_span_X_image [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext d
      rw [map_zero]
      exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [h0]
    exact Ideal.zero_mem _
  | @insert s T hs ih =>
    intro f hf

    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q, hq⟩ := hdvd
    have hmem₀ : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' (T : Set σ)) := by
      apply ih
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl
    have hsub : Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' ((insert s T : Finset σ) : Set σ)) := by
      apply Ideal.span_mono
      apply Set.image_mono
      simp
    have hX : (X s : MvPowerSeries σ R) ∈
        Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' ((insert s T : Finset σ) : Set σ)) :=
      Ideal.subset_span ⟨s, by simp, rfl⟩
    have hf01 : f = f₀ + X s * q := by rw [← hq]; ring
    rw [hf01]
    exact Ideal.add_mem _ (hsub hmem₀) (Ideal.mul_mem_right _ _ hX)

theorem mem_span_range_X_of_constantCoeff [Fintype σ] {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  classical
  have h := mem_span_X_image (R := R) (Finset.univ : Finset σ) f (fun d hd => by
    have hd0 : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [hd0, coeff_zero_eq_constantCoeff_apply, hf])
  simpa [Set.image_univ] using h

theorem subst_mem_span_of_constantCoeff [Fintype σ] {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (mem_span_range_X_of_constantCoeff hf)
  rw [← hc, ← coe_substAlgHom ha, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, coe_substAlgHom ha, subst_X ha]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨s, rfl⟩)

end Peel

end MvFormalGroup.C1Kit

namespace KerPiSmooth

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.MvFormalGroup P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.MvFormalGroup.C1Kit CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld.FormalODModule"

theorem smooth_case {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (χ : Zp2 q →+* k) (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k)
    (hΓ : X₀.F.IsSymmTwoCocycle Γ) (hΓ' : X₀.F.IsSymmTwoCocycle Γ')
    (hΓt : ∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      MvPowerSeries.subst (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.act a i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.act a i)) Γ = χ a • Γ + X₀.F.addCoboundary g)
    (hΓ't : ∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      MvPowerSeries.subst (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.act a i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.act a i)) Γ' = χ a • Γ' + X₀.F.addCoboundary g)
    (hΓk : ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      MvPowerSeries.subst (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)) Γ = X₀.F.addCoboundary g)
    (hΓ'k : ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
      MvPowerSeries.subst (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)) Γ' = X₀.F.addCoboundary g) :
    ∃ (c c' : k) (g : MvPowerSeries (Fin 2) k), (c ≠ 0 ∨ c' ≠ 0) ∧ MvPowerSeries.constantCoeff g = 0 ∧
      c • Γ + c' • Γ' = X₀.F.addCoboundary g := by
  classical
  haveI := X₀.isComm
  set X := X₀.toFormalODModule with hXdef
  have hv := X₀.isLawHom_varpi

  have hh : Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X₀.F.nthSeries q))) = q ^ 4 := by
    obtain ⟨-, -, hdeg⟩ := X₀.hasHeight
    have h1 := hdeg k (RingHom.id k)
    have e : (X₀.act (q : Zp2 q)).map (RingHom.id k) = X₀.F.nthSeries q := by
      rw [← X₀.act_natCast]; funext i; simp [Series.map]
    rw [e] at h1
    exact h1

  have hIJ : Ideal.span (Set.range (X₀.F.nthSeries q)) ≤ Ideal.span (Set.range X₀.varpi) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← X₀.act_natCast, ← X₀.varpi_comp_varpi]
    exact subst_mem_span_of_constantCoeff hv.hasSubst (hv.1 i)
  have hfin : Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi)) := by
    haveI : Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X₀.F.nthSeries q))) :=
      Module.finite_of_finrank_pos (by rw [hh]; exact pow_pos (Fact.out : q.Prime).pos 4)
    exact Module.Finite.of_surjective
      (Ideal.Quotient.factorₐ k hIJ).toLinearMap (Ideal.Quotient.factor_surjective hIJ)

  have hread : ∀ {Δ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} {gΔ : MvPowerSeries (Fin 2) k},
      X₀.F.IsSymmTwoCocycle Δ →
      (∀ a : Zp2 q, X.F.Cob (X.PA a Δ) (χ a • Δ)) →
      MvPowerSeries.constantCoeff gΔ = 0 →
      subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) Δ = X₀.F.addCoboundary gΔ →
      ∀ a : Zp2 q, subst (X₀.act a) gΔ - χ (WittVector.frobenius a) • gΔ ∈ Ideal.span (Set.range X₀.varpi) := by
    intro Δ gΔ hΔ hT hg0 hg a
    have ha := X₀.isLawHom_act a
    obtain ⟨b, hb0, hb⟩ := hT (WittVector.frobenius a)

    have e1 : subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a)))
        (subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) Δ)
        = X₀.F.addCoboundary (subst (X₀.act a) gΔ) := by
      rw [hg, pull_addCoboundary X₀.F ha.1 ha.2]
    have e2 : subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a)))
        (subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) Δ)
        = X₀.F.addCoboundary (χ (WittVector.frobenius a) • gΔ + subst X₀.varpi b) := by
      rw [← pull_comp hv.1 ha.1]
      have hc : (fun i => subst (X₀.act a) (X₀.varpi i)) = X₀.varpi.comp (X₀.act a) := rfl
      rw [hc, X₀.varpi_comp_act a]
      show subst (Sum.elim (inL fun i => subst X₀.varpi (X₀.act (WittVector.frobenius a) i))
          (inR fun i => subst X₀.varpi (X₀.act (WittVector.frobenius a) i))) Δ = _
      rw [pull_comp (X₀.isLawHom_act _).1 hv.1]
      have hb' : X.PA (WittVector.frobenius a) Δ = χ (WittVector.frobenius a) • Δ + X₀.F.addCoboundary b := hb
      show subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) (X.PA (WittVector.frobenius a) Δ) = _
      rw [hb', pull_add hv.1, pull_smul hv.1, pull_addCoboundary X₀.F hv.1 hv.2, hg, addCoboundary_add,
        addCoboundary_smul]
    have e3 : X₀.F.addCoboundary (subst (X₀.act a) gΔ - (χ (WittVector.frobenius a) • gΔ + subst X₀.varpi b)) = 0 := by
      rw [addCoboundary_sub', ← e1, ← e2, sub_self]
    have e4 := MvFormalGroup.eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow q X₀.F 4 hh
      _ (by
        rw [map_sub, map_add, MvPowerSeries.constantCoeff_smul, hg0, smul_zero, zero_add,
          constantCoeff_subst_eq_zero ha.hasSubst ha.1 hg0,
          constantCoeff_subst_eq_zero hv.hasSubst hv.1 hb0, sub_self]) e3
    have e5 : subst (X₀.act a) gΔ - χ (WittVector.frobenius a) • gΔ = subst X₀.varpi b := by
      linear_combination e4
    rw [e5]
    exact subst_mem_span_of_constantCoeff hv.hasSubst hb0

  have hprim : ∀ {Δ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} {gΔ : MvPowerSeries (Fin 2) k},
      X₀.F.IsSymmTwoCocycle Δ →
      subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) Δ = X₀.F.addCoboundary gΔ →
      X₀.F.addCoboundary gΔ ∈ Ideal.span (Set.range (Sum.elim (inL X₀.varpi) (inR X₀.varpi))) := by
    intro Δ gΔ hΔ hg
    rw [← hg]
    exact subst_mem_span_of_constantCoeff (hasSubst_pull hv.1) hΔ.constantCoeff_eq_zero

  obtain ⟨g, hg0, hg⟩ := hΓk
  obtain ⟨g', hg0', hg'⟩ := hΓ'k
  have hTc : ∀ a, X.F.Cob (X.PA a Γ) (χ a • Γ) := fun a => hΓt a
  have hTc' : ∀ a, X.F.Cob (X.PA a Γ') (χ a • Γ') := fun a => hΓ't a

  obtain ⟨c, c', hcc, hmem⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_not_and
      X₀ hsmooth (fun a => χ (WittVector.frobenius a)) g g' hg0 hg0' (hprim hΓ hg) (hprim hΓ' hg')
      (hread hΓ hTc hg0 hg) (hread hΓ' hTc' hg0' hg')

  have hcoc : X₀.F.IsSymmTwoCocycle (c • Γ + c' • Γ') :=
    IsSymmTwoCocycle.add' X₀.F (IsSymmTwoCocycle.smul' X₀.F c hΓ) (IsSymmTwoCocycle.smul' X₀.F c' hΓ')
  have hpull : subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) (c • Γ + c' • Γ')
      = X₀.F.addCoboundary (c • g + c' • g') := by
    rw [pull_smul_add hv.1, pull_smul hv.1, hg, hg', addCoboundary_add, addCoboundary_smul, addCoboundary_smul]
  obtain ⟨G, hG0, -, hG⟩ :=
    MvFormalGroup.exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span X₀.F X₀.varpi hv.1 hv.2
      hfin (c • Γ + c' • Γ') hcoc (c • g + c' • g')
      (by rw [map_add, MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_smul, hg0, hg0', smul_zero,
        smul_zero, add_zero]) hpull hmem
  exact ⟨c, c', G, hcc, hG0, hG⟩

end KerPiSmooth

noncomputable section

namespace KerPiNode

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld.FormalODModule"
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable {q : ℕ} [Fact q.Prime]

section kit

variable {k : Type u} [Field k]

section cocycles

variable {n : ℕ} {F₀ : MvFormalGroup n k}

theorem isSymmTwoCocycle_add {Γ₁ Γ₂ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (h₁ : F₀.IsSymmTwoCocycle Γ₁) (h₂ : F₀.IsSymmTwoCocycle Γ₂) :
    F₀.IsSymmTwoCocycle (Γ₁ + Γ₂) := by
  have hA : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB := MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC := MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  refine ⟨by rw [map_add, h₁.constantCoeff_eq_zero, h₂.constantCoeff_eq_zero, add_zero], ?_, ?_⟩
  · rw [MvPowerSeries.subst_add (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)),
      h₁.symm, h₂.symm]
  · rw [MvPowerSeries.subst_add (MvFormalGroup.hasSubst_elim hFAB hC),
      MvPowerSeries.subst_add (MvFormalGroup.hasSubst_elim hA hB),
      MvPowerSeries.subst_add (MvFormalGroup.hasSubst_elim hA hFBC),
      MvPowerSeries.subst_add (MvFormalGroup.hasSubst_elim hB hC)]
    have e₁ := h₁.cocycle
    have e₂ := h₂.cocycle
    linear_combination e₁ + e₂

theorem isSymmTwoCocycle_smul (a : k) {Γ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (h : F₀.IsSymmTwoCocycle Γ) : F₀.IsSymmTwoCocycle (a • Γ) := by
  have hA : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB := MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC := MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  refine ⟨by rw [MvPowerSeries.constantCoeff_smul, h.constantCoeff_eq_zero, smul_zero], ?_, ?_⟩
  · rw [MvPowerSeries.subst_smul (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)),
      h.symm]
  · rw [MvPowerSeries.subst_smul (MvFormalGroup.hasSubst_elim hFAB hC),
      MvPowerSeries.subst_smul (MvFormalGroup.hasSubst_elim hA hB),
      MvPowerSeries.subst_smul (MvFormalGroup.hasSubst_elim hA hFBC),
      MvPowerSeries.subst_smul (MvFormalGroup.hasSubst_elim hB hC),
      ← smul_add, ← smul_add, h.cocycle]

variable (F₀)

theorem hasSubst_Xl : HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_Xr : HasSubst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem addCoboundary_add (g₁ g₂ : MvPowerSeries (Fin n) k) :
    F₀.addCoboundary (g₁ + g₂) = F₀.addCoboundary g₁ + F₀.addCoboundary g₂ := by
  unfold MvFormalGroup.addCoboundary
  rw [MvPowerSeries.subst_add F₀.hasSubst_toPowerSeries, MvPowerSeries.subst_add (hasSubst_Xl (k := k)),
    MvPowerSeries.subst_add (hasSubst_Xr (k := k))]
  ring

theorem addCoboundary_smul (a : k) (g : MvPowerSeries (Fin n) k) :
    F₀.addCoboundary (a • g) = a • F₀.addCoboundary g := by
  unfold MvFormalGroup.addCoboundary
  rw [MvPowerSeries.subst_smul F₀.hasSubst_toPowerSeries, MvPowerSeries.subst_smul (hasSubst_Xl (k := k)),
    MvPowerSeries.subst_smul (hasSubst_Xr (k := k)), smul_sub, smul_sub]

theorem addCoboundary_zero : F₀.addCoboundary 0 = 0 := by
  have h := addCoboundary_smul F₀ (0 : k) 0
  rwa [zero_smul, zero_smul] at h

theorem addCoboundary_neg (g : MvPowerSeries (Fin n) k) :
    F₀.addCoboundary (- g) = - F₀.addCoboundary g := by
  have h := addCoboundary_smul F₀ (-1 : k) g
  rwa [neg_one_smul, neg_one_smul] at h

end cocycles

end kit

end KerPiNode

namespace KerPiNode
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

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld.FormalODModule"
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable {q : ℕ} [Fact q.Prime]

section node

variable {k : Type u} [Field k] [CharP k q] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

def pullF (φ : Series k) : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  Sum.elim
    (fun i => subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
    fun i => subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i)

omit X₀ in
theorem pullF_cc {φ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) (s : Fin 2 ⊕ Fin 2) :
    constantCoeff (pullF φ s) = 0 := by
  rcases s with i | i
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _)
      (fun m => constantCoeff_X _) (hφ i)
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _)
      (fun m => constantCoeff_X _) (hφ i)

omit X₀ in
theorem hasSubst_pullF {φ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) : HasSubst (pullF φ) :=
  hasSubst_of_constantCoeff_zero (pullF_cc hφ)

omit X₀ in

theorem pull_pull {φ ψ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) :
    subst (pullF ψ) (subst (pullF φ) Γ) = subst (pullF (φ.comp ψ)) Γ := by
  rw [subst_comp_subst_apply (hasSubst_pullF hφ) (hasSubst_pullF hψ)]
  congr 1
  funext s
  rcases s with i | i
  · show subst (pullF ψ) (subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i)) =
      subst (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (subst ψ (φ i))
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _) (hasSubst_pullF hψ),
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ)
        (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _)]
    congr 1
    funext m
    rw [subst_X (hasSubst_pullF hψ)]
    rfl
  · show subst (pullF ψ) (subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i)) =
      subst (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (subst ψ (φ i))
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _) (hasSubst_pullF hψ),
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ)
        (hasSubst_of_constantCoeff_zero fun m => constantCoeff_X _)]
    congr 1
    funext m
    rw [subst_X (hasSubst_pullF hψ)]
    rfl

theorem act_cc (a : Zp2 q) : ∀ i, constantCoeff (X₀.act a i) = 0 := (X₀.isLawHom_act a).1
theorem varpi_cc : ∀ i, constantCoeff (X₀.varpi i) = 0 := X₀.isLawHom_varpi.1

theorem pull_act_addCoboundary (a : Zp2 q) (g : MvPowerSeries (Fin 2) k) (hg : constantCoeff g = 0) :
    constantCoeff (subst (X₀.act a) g) = 0 ∧
      subst (pullF (X₀.act a)) (X₀.F.addCoboundary g) = X₀.F.addCoboundary (subst (X₀.act a) g) :=
  ((CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add X₀).1 (X₀.act a)
    (Or.inr ⟨a, rfl⟩)).2 g hg

theorem pull_varpi_addCoboundary (g : MvPowerSeries (Fin 2) k) (hg : constantCoeff g = 0) :
    constantCoeff (subst X₀.varpi g) = 0 ∧
      subst (pullF X₀.varpi) (X₀.F.addCoboundary g) = X₀.F.addCoboundary (subst X₀.varpi g) :=
  ((CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add X₀).1 X₀.varpi
    (Or.inl rfl)).2 g hg

theorem hh₀ : Module.finrank k (MvPowerSeries (Fin 2) k ⧸
    Ideal.span (Set.range (X₀.F.nthSeries q))) = q ^ 4 := by
  obtain ⟨-, -, hrank⟩ := X₀.hasHeight
  have h0 := hrank k (RingHom.id k)
  rw [Series.map_ringHom_id] at h0
  rw [← FormalODModule.act_natCast]
  exact h0

theorem eq_of_addCoboundary_eq {g g' : MvPowerSeries (Fin 2) k} (hg : constantCoeff g = 0)
    (hg' : constantCoeff g' = 0) (h : X₀.F.addCoboundary g = X₀.F.addCoboundary g') : g = g' := by
  have h0 : X₀.F.addCoboundary (g - g') = 0 := by
    rw [sub_eq_add_neg, addCoboundary_add, addCoboundary_neg, h, add_neg_cancel]
  have := MvFormalGroup.eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow q X₀.F 4
    (hh₀ X₀) (g - g') (by rw [map_sub, hg, hg', sub_zero]) h0
  exact sub_eq_zero.mp this

theorem linearPart_varpi_eq_zero
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) :
    MvFormalGroup.linearPart X₀.varpi = 0 := by
  have htop : X₀.toFormalODModule.lieZero j₀ ⊔ X₀.toFormalODModule.lieOne j₀ = ⊤ := X₀.isSpecial.1.sup_eq_top
  have hall : ∀ m : Fin 2 → k, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0 := by
    intro m
    have hm : m ∈ X₀.toFormalODModule.lieZero j₀ ⊔ X₀.toFormalODModule.lieOne j₀ := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hm
    rw [map_add, hnode₀ y hy, hnode₁ z hz, add_zero]
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have h := hall (Pi.single i 1)
  rw [Matrix.mulVecLin_apply] at h
  rw [h, Matrix.zero_mulVec]

theorem lin_subst {φ : Series k} (hφ : ∀ i, constantCoeff (φ i) = 0) (g : MvPowerSeries (Fin 2) k) (m : Fin 2) :
    coeff (Finsupp.single m 1) (subst φ g) =
      ∑ i, coeff (Finsupp.single i 1) g * MvFormalGroup.linearPart φ i m := by
  rw [MvFormalGroup.coeff_single_subst hφ g m]
  rfl

theorem eig_zero {v : Fin 2 → k} (hv : v ∈ X₀.toFormalODModule.lieZero j₀) (a : Zp2 q) :
    (MvFormalGroup.linearPart (X₀.act a)).mulVec v = j₀ a • v := by
  have h : v ∈ ⨅ a : Zp2 q, LinearMap.ker (X₀.toFormalODModule.lieAct a - j₀ a • LinearMap.id) := hv
  rw [Submodule.mem_iInf] at h
  have h' := h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h'
  exact h'

theorem eig_one {v : Fin 2 → k} (hv : v ∈ X₀.toFormalODModule.lieOne j₀) (a : Zp2 q) :
    (MvFormalGroup.linearPart (X₀.act a)).mulVec v = j₀ (WittVector.frobenius a) • v := by
  have h : v ∈ ⨅ a : Zp2 q,
      LinearMap.ker (X₀.toFormalODModule.lieAct a - j₀ (WittVector.frobenius a) • LinearMap.id) := hv
  rw [Submodule.mem_iInf] at h
  have h' := h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h'
  exact h'

theorem exists_eig_zero : ∃ v ∈ X₀.toFormalODModule.lieZero j₀, v ≠ 0 := by
  haveI : Module.Invertible k (X₀.toFormalODModule.lieZero j₀) := X₀.isSpecial.2.1
  have h1 : Module.finrank k (X₀.toFormalODModule.lieZero j₀) = 1 := Module.Invertible.finrank_eq_one k _
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)
    (M := X₀.toFormalODModule.lieZero j₀)).mp (by omega)
  exact ⟨v, v.2, fun h => hv (Subtype.ext h)⟩

theorem exists_eig_one : ∃ v ∈ X₀.toFormalODModule.lieOne j₀, v ≠ 0 := by
  haveI : Module.Invertible k (X₀.toFormalODModule.lieOne j₀) := X₀.isSpecial.2.2
  have h1 : Module.finrank k (X₀.toFormalODModule.lieOne j₀) = 1 := Module.Invertible.finrank_eq_one k _
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)
    (M := X₀.toFormalODModule.lieOne j₀)).mp (by omega)
  exact ⟨v, v.2, fun h => hv (Subtype.ext h)⟩

omit X₀ in

theorem dep_of_orth {v w w' : Fin 2 → k} (hv : v ≠ 0)
    (hw : w 0 * v 0 + w 1 * v 1 = 0) (hw' : w' 0 * v 0 + w' 1 * v 1 = 0) :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • w + c' • w' = 0 := by
  have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
  rcases hne with h0 | h1
  · by_cases hz : w 1 = 0 ∧ w' 1 = 0
    · have hw0 : w 0 = 0 := by
        have : w 0 * v 0 = 0 := by rw [hz.1, zero_mul, add_zero] at hw; exact hw
        exact (mul_eq_zero.mp this).resolve_right h0
      refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      funext i; fin_cases i
      · show 1 * w 0 + 0 * w' 0 = 0; rw [hw0]; ring
      · show 1 * w 1 + 0 * w' 1 = 0; rw [hz.1]; ring
    · refine ⟨w' 1, -(w 1), ?_, ?_⟩
      · by_contra hc; push_neg at hc; exact hz ⟨neg_eq_zero.mp hc.2, hc.1⟩
      · funext i; fin_cases i
        · show w' 1 * w 0 + -(w 1) * w' 0 = 0
          have : (w' 1 * w 0 + -(w 1) * w' 0) * v 0 = 0 := by linear_combination (w' 1) * hw - (w 1) * hw'
          exact (mul_eq_zero.mp this).resolve_right h0
        · show w' 1 * w 1 + -(w 1) * w' 1 = 0; ring
  · by_cases hz : w 0 = 0 ∧ w' 0 = 0
    · have hw1 : w 1 = 0 := by
        have : w 1 * v 1 = 0 := by rw [hz.1, zero_mul, zero_add] at hw; exact hw
        exact (mul_eq_zero.mp this).resolve_right h1
      refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      funext i; fin_cases i
      · show 1 * w 0 + 0 * w' 0 = 0; rw [hz.1]; ring
      · show 1 * w 1 + 0 * w' 1 = 0; rw [hw1]; ring
    · refine ⟨w' 0, -(w 0), ?_, ?_⟩
      · by_contra hc; push_neg at hc; exact hz ⟨neg_eq_zero.mp hc.2, hc.1⟩
      · funext i; fin_cases i
        · show w' 0 * w 0 + -(w 0) * w' 0 = 0; ring
        · show w' 0 * w 1 + -(w 0) * w' 1 = 0
          have : (w' 0 * w 1 + -(w 0) * w' 1) * v 1 = 0 := by linear_combination (w' 0) * hw - (w 0) * hw'
          exact (mul_eq_zero.mp this).resolve_right h1

theorem dep_of_roweig (μ : Zp2 q → k) {w w' : Fin 2 → k}
    (hw : ∀ a m, ∑ i, w i * MvFormalGroup.linearPart (X₀.act a) i m = μ a * w m)
    (hw' : ∀ a m, ∑ i, w' i * MvFormalGroup.linearPart (X₀.act a) i m = μ a * w' m) :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • w + c' • w' = 0 := by
  obtain ⟨v₀, hv₀m, hv₀⟩ := exists_eig_zero X₀
  obtain ⟨v₁, hv₁m, hv₁⟩ := exists_eig_one X₀

  have pair : ∀ {u v : Fin 2 → k} {ν : k} (a : Zp2 q),
      (∀ m, ∑ i, u i * MvFormalGroup.linearPart (X₀.act a) i m = μ a * u m) →
      (MvFormalGroup.linearPart (X₀.act a)).mulVec v = ν • v →
      (μ a - ν) * (u 0 * v 0 + u 1 * v 1) = 0 := by
    intro u v ν a hu hv
    have hv' : ∀ i, MvFormalGroup.linearPart (X₀.act a) i 0 * v 0 +
        MvFormalGroup.linearPart (X₀.act a) i 1 * v 1 = ν * v i := fun i => by
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have hu' : ∀ m, u 0 * MvFormalGroup.linearPart (X₀.act a) 0 m +
        u 1 * MvFormalGroup.linearPart (X₀.act a) 1 m = μ a * u m := fun m => by
      have := hu m
      simpa [Fin.sum_univ_two] using this
    linear_combination (u 0) * hv' 0 + (u 1) * hv' 1 - (v 0) * hu' 0 - (v 1) * hu' 1
  obtain ⟨z, hz⟩ := C1cKit.exists_isUnit_sub_frobenius q
  have hzne : j₀ z ≠ j₀ (WittVector.frobenius z) := by
    intro he
    have hu := (hz.map j₀)
    rw [map_sub, he, sub_self] at hu
    exact not_isUnit_zero hu
  by_cases hμ : μ z = j₀ z
  ·
    have hne : μ z - j₀ (WittVector.frobenius z) ≠ 0 := by rw [hμ]; exact sub_ne_zero.mpr hzne
    have o := fun {u : Fin 2 → k} (hu : ∀ a m, ∑ i, u i * MvFormalGroup.linearPart (X₀.act a) i m = μ a * u m) =>
      (mul_eq_zero.mp (pair z (hu z) (eig_one X₀ hv₁m z))).resolve_left hne
    exact dep_of_orth hv₁ (o hw) (o hw')
  · have hne : μ z - j₀ z ≠ 0 := sub_ne_zero.mpr hμ
    have o := fun {u : Fin 2 → k} (hu : ∀ a m, ∑ i, u i * MvFormalGroup.linearPart (X₀.act a) i m = μ a * u m) =>
      (mul_eq_zero.mp (pair z (hu z) (eig_zero X₀ hv₀m z))).resolve_left hne
    exact dep_of_orth hv₀ (o hw) (o hw')

theorem roweig_of_type (hlam : MvFormalGroup.linearPart X₀.varpi = 0) (χ : Zp2 q →+* k)
    {Δ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} {h : MvPowerSeries (Fin 2) k}
    (hΔt : ∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧
        subst (pullF (X₀.act a)) Δ = χ a • Δ + X₀.F.addCoboundary g)
    (hh0 : constantCoeff h = 0) (hh : subst (pullF X₀.varpi) Δ = X₀.F.addCoboundary h) :
    ∀ a m, ∑ i, coeff (Finsupp.single i 1) h * MvFormalGroup.linearPart (X₀.act a) i m =
      χ (WittVector.frobenius a) * coeff (Finsupp.single m 1) h := by
  intro a m
  obtain ⟨b, hb0, hb⟩ := hΔt (WittVector.frobenius a)
  have e1 : subst (pullF (X₀.act a)) (subst (pullF X₀.varpi) Δ) = X₀.F.addCoboundary (subst (X₀.act a) h) := by
    rw [hh]; exact (pull_act_addCoboundary X₀ a h hh0).2
  have e2 : subst (pullF (X₀.act a)) (subst (pullF X₀.varpi) Δ) =
      X₀.F.addCoboundary (χ (WittVector.frobenius a) • h + subst X₀.varpi b) := by
    rw [pull_pull (varpi_cc X₀) (act_cc X₀ a), X₀.varpi_comp_act a,
      ← pull_pull (act_cc X₀ (WittVector.frobenius a)) (varpi_cc X₀), hb,
      MvPowerSeries.subst_add (hasSubst_pullF (varpi_cc X₀)),
      MvPowerSeries.subst_smul (hasSubst_pullF (varpi_cc X₀)), hh,
      (pull_varpi_addCoboundary X₀ b hb0).2, addCoboundary_add, addCoboundary_smul]
  have e3 : subst (X₀.act a) h = χ (WittVector.frobenius a) • h + subst X₀.varpi b :=
    eq_of_addCoboundary_eq X₀ (pull_act_addCoboundary X₀ a h hh0).1
      (by rw [map_add, MvPowerSeries.constantCoeff_smul, hh0, smul_zero, zero_add]
          exact (pull_varpi_addCoboundary X₀ b hb0).1)
      (e1.symm.trans e2)
  have e4 := congrArg (coeff (Finsupp.single m 1)) e3
  rw [lin_subst (act_cc X₀ a), map_add, MvPowerSeries.coeff_smul, lin_subst (varpi_cc X₀)] at e4
  simp only [hlam, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, smul_eq_mul] at e4
  exact e4

theorem node_case [IsAlgClosed k]
    (hnode : (∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
    (χ : Zp2 q →+* k) (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k)
    (hΓ : X₀.F.IsSymmTwoCocycle Γ) (hΓ' : X₀.F.IsSymmTwoCocycle Γ')
    (hΓt : ∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧
        subst (pullF (X₀.act a)) Γ = χ a • Γ + X₀.F.addCoboundary g)
    (hΓ't : ∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧
        subst (pullF (X₀.act a)) Γ' = χ a • Γ' + X₀.F.addCoboundary g)
    (hΓk : ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧ subst (pullF X₀.varpi) Γ = X₀.F.addCoboundary g)
    (hΓ'k : ∃ g : MvPowerSeries (Fin 2) k, constantCoeff g = 0 ∧ subst (pullF X₀.varpi) Γ' = X₀.F.addCoboundary g) :
    ∃ (c c' : k) (g : MvPowerSeries (Fin 2) k), (c ≠ 0 ∨ c' ≠ 0) ∧ constantCoeff g = 0 ∧
      c • Γ + c' • Γ' = X₀.F.addCoboundary g := by
  obtain ⟨g, hg0, hg⟩ := hΓk
  obtain ⟨g', hg0', hg'⟩ := hΓ'k
  have hlam := linearPart_varpi_eq_zero X₀ hnode.1 hnode.2
  have rw_ := roweig_of_type X₀ hlam χ hΓt hg0 hg
  have rw' := roweig_of_type X₀ hlam χ hΓ't hg0' hg'
  obtain ⟨c, c', hcc, hdep⟩ := dep_of_roweig X₀ (fun a => χ (WittVector.frobenius a)) rw_ rw'

  have hG0 : constantCoeff (c • g + c' • g') = 0 := by
    rw [map_add, MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_smul, hg0, hg0', smul_zero, smul_zero,
      add_zero]
  have hGlin : ∀ m, coeff (Finsupp.single m 1) (c • g + c' • g') = 0 := fun m => by
    have := congrFun hdep m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [map_add, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul]
    exact this
  have hcoc : X₀.F.IsSymmTwoCocycle (c • Γ + c' • Γ') :=
    isSymmTwoCocycle_add (isSymmTwoCocycle_smul c hΓ) (isSymmTwoCocycle_smul c' hΓ')
  have hpull : subst (pullF X₀.varpi) (c • Γ + c' • Γ') = X₀.F.addCoboundary (c • g + c' • g') := by
    rw [MvPowerSeries.subst_add (hasSubst_pullF (varpi_cc X₀)),
      MvPowerSeries.subst_smul (hasSubst_pullF (varpi_cc X₀)),
      MvPowerSeries.subst_smul (hasSubst_pullF (varpi_cc X₀)), hg, hg', addCoboundary_add, addCoboundary_smul,
      addCoboundary_smul]
  obtain ⟨b, hb0, hb⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
      X₀ hnode.1 hnode.2 (c • Γ + c' • Γ') hcoc (c • g + c' • g') hG0 hGlin hpull
  exact ⟨c, c', b, hcc, hb0, hb⟩

end node

end KerPiNode

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) (χ : Zp2 q →+* k)
    (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : X₀.F.IsSymmTwoCocycle Γ) (hΓ' : X₀.F.IsSymmTwoCocycle Γ') :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    (∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull (X₀.act a) Γ = χ a • Γ + X₀.F.addCoboundary g) →
    (∀ a : Zp2 q, ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull (X₀.act a) Γ' = χ a • Γ' + X₀.F.addCoboundary g) →
    (∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull X₀.varpi Γ = X₀.F.addCoboundary g) →
    (∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull X₀.varpi Γ' = X₀.F.addCoboundary g) →
    ∃ (c c' : k) (g : MvPowerSeries (Fin 2) k), (c ≠ 0 ∨ c' ≠ 0) ∧ MvPowerSeries.constantCoeff g = 0 ∧
      c • Γ + c' • Γ' = X₀.F.addCoboundary g := by
  intro pull hΓt hΓ't hΓk hΓ'k
  by_cases h : ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
  · exact KerPiNode.node_case X₀ h χ Γ Γ' hΓ hΓ' hΓt hΓ't hΓk hΓ'k
  · exact KerPiSmooth.smooth_case X₀ h χ Γ Γ' hΓ hΓ' hΓt hΓ't hΓk hΓ'k

end

end S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_eq_addCoboundary_of_type_of_subst_varpi_eq_addCoboundary (solution)
