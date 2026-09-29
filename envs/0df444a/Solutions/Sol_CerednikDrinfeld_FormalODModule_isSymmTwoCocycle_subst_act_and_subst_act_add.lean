-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isSymmTwoCocycle_subst_act_and_subst_act_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3ecb6386-3ff1-5dc2-a53f-05b047de79aa

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add

set_option autoImplicit false

universe u

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormalODModule" namespace FormalODModule p2m_export "CerednikDrinfeld.FormalODModule" "F varpi act_mul isLawHom_act act_add act_one isComm act isLawHom_varpi" end CerednikDrinfeld.FormalODModule
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalODModule" in
open MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add.MvFormalGroup MvFormalGroup.C1Kit _root_.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

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
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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
p2m_export "MvFormalGroup" "hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm IsComm hasSubst_toPowerSeries toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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

open MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add.MvFormalGroup MvFormalGroup.C1Kit in
open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ

    (∀ φ : Fin 2 → MvPowerSeries (Fin 2) k, (φ = X₀.varpi ∨ ∃ a, φ = X₀.act a) →
      (∀ Γ, X₀.F.IsSymmTwoCocycle Γ → X₀.F.IsSymmTwoCocycle (pull φ Γ)) ∧
      (∀ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 →
        MvPowerSeries.constantCoeff (MvPowerSeries.subst φ g) = 0 ∧
        pull φ (X₀.F.addCoboundary g) = X₀.F.addCoboundary (MvPowerSeries.subst φ g))) ∧

    (∀ (a b : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      pull (X₀.act (a * b)) Γ = pull (X₀.act b) (pull (X₀.act a) Γ)) ∧
    (∀ Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, pull (X₀.act 1) Γ = Γ) ∧

    (∀ (a b : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k), X₀.F.IsSymmTwoCocycle Γ →
      ∃ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 ∧
        pull (X₀.act (a + b)) Γ = pull (X₀.act a) Γ + pull (X₀.act b) Γ + X₀.F.addCoboundary g) := by
  intro pull
  haveI := X₀.isComm
  refine ⟨fun φ hφ => ?_, fun a b Γ => ?_, fun Γ => ?_, fun a b Γ hΓ => ?_⟩
  ·
    have hlaw : IsLawHom X₀.F X₀.F φ := by
      rcases hφ with rfl | ⟨a, rfl⟩
      · exact X₀.isLawHom_varpi
      · exact X₀.isLawHom_act a
    refine ⟨fun Γ hΓ => isSymmTwoCocycle_pull X₀.F hΓ hlaw.1 hlaw.2, fun g₁ hg₁ => ⟨?_, ?_⟩⟩
    · exact constantCoeff_subst_eq_zero hlaw.hasSubst hlaw.1 hg₁
    · exact pull_addCoboundary X₀.F hlaw.1 hlaw.2 g₁
  ·
    rw [X₀.act_mul]
    exact pull_comp (X₀.isLawHom_act a).1 (X₀.isLawHom_act b).1 Γ
  ·
    rw [X₀.act_one]
    exact pull_X Γ
  ·
    exact CerednikDrinfeld.FormalODModule.exists_pull_act_add X₀.toFormalODModule a b Γ hΓ

end S_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isSymmTwoCocycle_subst_act_and_subst_act_add (solution)
