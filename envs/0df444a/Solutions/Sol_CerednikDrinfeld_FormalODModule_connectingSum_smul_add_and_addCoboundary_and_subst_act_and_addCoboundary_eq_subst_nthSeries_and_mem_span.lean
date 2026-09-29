-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0a69cd51-d3cc-5c09-9f0d-c48eadb3caf8

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span

set_option autoImplicit false

universe u

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries Hom map nthSeries nthSeries_zero toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries Hom map nthSeries nthSeries_zero toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Zp2 FormalODModule" namespace FormalODModule p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast Hom varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi" end CerednikDrinfeld.FormalODModule
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalODModule" in
open MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.MvFormalGroup MvFormalGroup.C1Kit _root_.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

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
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries Hom map nthSeries nthSeries_zero toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries Hom map nthSeries nthSeries_zero toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries Hom map nthSeries nthSeries_zero toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast Hom varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi"
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.MvFormalGroup P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.MvFormalGroup.C1Kit CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

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

namespace MvFormalGroup
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries Hom map nthSeries nthSeries_zero toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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

end MvFormalGroup

namespace MvFormalGroup
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries Hom map nthSeries nthSeries_zero toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
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

namespace MvFormalGroup
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm constantCoeff_nthSeries IsComm hasSubst_toPowerSeries Hom map nthSeries nthSeries_zero toPowerSeries constantCoeff_eq_zero addCoboundary IsSymmTwoCocycle"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R)

theorem hasSubst_nthPair (n : ℕ) :
    HasSubst (Sum.elim (F.nthSeries n) fun l => (X l : MvPowerSeries (Fin g) R)) :=
  hasSubst_elim (constantCoeff_nthSeries F n) (fun l => constantCoeff_X l)

theorem sum_range_telescope {M : Type*} [AddCommGroup M] (f : ℕ → M) (c : M) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + 1) - f i - c) = f n - f 0 - n • c := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, succ_nsmul]; abel

theorem addCoboundary_sum {ι : Type*} (s : Finset ι) (h : ι → MvPowerSeries (Fin g) R) :
    F.addCoboundary (∑ i ∈ s, h i) = ∑ i ∈ s, F.addCoboundary (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, addCoboundary_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, addCoboundary_add, ih]

theorem nthPair_addCoboundary (n : ℕ) (g₁ : MvPowerSeries (Fin g) R) :
    subst (Sum.elim (F.nthSeries n) fun l => (X l : MvPowerSeries (Fin g) R)) (F.addCoboundary g₁)
      = subst (F.nthSeries (n + 1)) g₁ - subst (F.nthSeries n) g₁ - g₁ := by
  have hT := hasSubst_nthPair F n
  rw [addCoboundary, subst_sub hT, subst_sub hT, subst_comp_subst_apply F.hasSubst_toPowerSeries hT,
    subst_comp_subst_apply hasSubst_XL hT, subst_comp_subst_apply hasSubst_XR hT]
  congr 2
  · congr 1; funext m; exact subst_X hT _
  · have e : ∀ (G : Fin g → MvPowerSeries (Fin g) R), G = X → subst G g₁ = g₁ := by
      rintro G rfl; exact congr_fun subst_self g₁
    exact e _ (funext fun m => subst_X hT _)

theorem theta_addCoboundary (q : ℕ) (g₁ : MvPowerSeries (Fin g) R) (hg : g₁.constantCoeff = 0) :
    ∑ i ∈ Finset.range q, subst (Sum.elim (F.nthSeries i) fun l => (X l : MvPowerSeries (Fin g) R))
        (F.addCoboundary g₁)
      = subst (F.nthSeries q) g₁ - q • g₁ := by
  simp_rw [nthPair_addCoboundary]
  rw [sum_range_telescope (fun i => subst (F.nthSeries i) g₁) g₁ q, nthSeries_zero,
    subst_zero_of_constantCoeff_eq_zero hg, sub_zero]

theorem subst_nthPair_comm (n : ℕ) {ψ : Fin g → MvPowerSeries (Fin g) R} (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (hcomm : ∀ j, subst ψ (F.nthSeries n j) = subst (F.nthSeries n) (ψ j))
    (Γ : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst ψ (subst (Sum.elim (F.nthSeries n) fun l => (X l : MvPowerSeries (Fin g) R)) Γ)
      = subst (Sum.elim (F.nthSeries n) fun l => (X l : MvPowerSeries (Fin g) R))
          (subst (Sum.elim (inL ψ) (inR ψ)) Γ) := by
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ
  rw [subst_comp_subst_apply (hasSubst_nthPair F n) hψs, subst_subst_pull (hasSubst_nthPair F n) hψ]
  congr 1
  funext s; rcases s with j | j
  · exact hcomm j
  · show subst ψ (X j) = subst (fun l => X l) (ψ j)
    rw [subst_X hψs]
    exact (congr_fun subst_self (ψ j)).symm

theorem addCoboundary_nthPair [IsComm F] (n : ℕ) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}
    (hΓ : F.IsSymmTwoCocycle Γ)
    (hNF : ∀ i, subst F.toPowerSeries (F.nthSeries n i)
      = subst (Sum.elim (inL (F.nthSeries n)) (inR (F.nthSeries n))) (F.toPowerSeries i)) :
    F.addCoboundary (subst (Sum.elim (F.nthSeries n) fun l => (X l : MvPowerSeries (Fin g) R)) Γ)
      = subst (Sum.elim (inL (F.nthSeries (n + 1))) (inR (F.nthSeries (n + 1)))) Γ
        - subst (Sum.elim (inL (F.nthSeries n)) (inR (F.nthSeries n))) Γ - Γ := by
  have hX : ∀ i, ((fun l => (X l : MvPowerSeries (Fin g) R)) i).constantCoeff = 0 := fun l => constantCoeff_X l
  have hXF : ∀ i, subst F.toPowerSeries ((fun l => (X l : MvPowerSeries (Fin g) R)) i)
      = subst (Sum.elim (inL fun l => (X l : MvPowerSeries (Fin g) R)) (inR fun l => X l)) (F.toPowerSeries i) := by
    intro i
    show subst F.toPowerSeries (X i) = _
    rw [subst_X F.hasSubst_toPowerSeries, pull_X]
  have h := pull_addVia F hΓ (constantCoeff_nthSeries F n) hX hNF hXF
  rw [pull_X] at h
  have e : (fun i => subst (Sum.elim (F.nthSeries n) fun l => (X l : MvPowerSeries (Fin g) R)) (F.toPowerSeries i))
      = F.nthSeries (n + 1) := rfl
  rw [e] at h
  linear_combination (-1 : MvPowerSeries (Fin g ⊕ Fin g) R) * h

theorem pull_nthSeries_zero {Γ : MvPowerSeries (Fin g ⊕ Fin g) R} (hΓ0 : Γ.constantCoeff = 0) :
    subst (Sum.elim (inL (F.nthSeries 0)) (inR (F.nthSeries 0))) Γ = 0 := by
  have e : Sum.elim (inL (F.nthSeries 0)) (inR (F.nthSeries 0))
      = fun _ : Fin g ⊕ Fin g => (0 : MvPowerSeries (Fin g ⊕ Fin g) R) := by
    funext s; rcases s with j | j
    · show subst _ ((fun _ => (0 : MvPowerSeries (Fin g) R)) j) = 0
      rw [← coe_substAlgHom hasSubst_XL, map_zero]
    · show subst _ ((fun _ => (0 : MvPowerSeries (Fin g) R)) j) = 0
      rw [← coe_substAlgHom hasSubst_XR, map_zero]
  rw [e, subst_zero_of_constantCoeff_eq_zero hΓ0]

theorem addCoboundary_theta [IsComm F] (q : ℕ) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}
    (hΓ : F.IsSymmTwoCocycle Γ)
    (hNF : ∀ n i, subst F.toPowerSeries (F.nthSeries n i)
      = subst (Sum.elim (inL (F.nthSeries n)) (inR (F.nthSeries n))) (F.toPowerSeries i)) :
    F.addCoboundary (∑ i ∈ Finset.range q,
        subst (Sum.elim (F.nthSeries i) fun l => (X l : MvPowerSeries (Fin g) R)) Γ)
      = subst (Sum.elim (inL (F.nthSeries q)) (inR (F.nthSeries q))) Γ - q • Γ := by
  rw [addCoboundary_sum]
  simp_rw [addCoboundary_nthPair F _ hΓ (hNF _)]
  rw [sum_range_telescope (fun i => subst (Sum.elim (inL (F.nthSeries i)) (inR (F.nthSeries i))) Γ) Γ q,
    pull_nthSeries_zero F hΓ.constantCoeff_eq_zero, sub_zero]

end MvFormalGroup.C1Kit

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule"
namespace FormalODModule
p2m_export "CerednikDrinfeld.FormalODModule" "map act_natCast Hom varpi_comp_act F varpi act_mul varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi"
p2m_open "CerednikDrinfeld.FormalODModule CerednikDrinfeld"

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.MvFormalGroup P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.MvFormalGroup.C1Kit CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] (X₀ : FormalODModule q k)

private theorem _root_.CerednikDrinfeld.FormalODModule.nthSeries_isLawHom (n : ℕ) : IsLawHom X₀.F X₀.F (X₀.F.nthSeries n) := by
  rw [← X₀.act_natCast]; exact X₀.isLawHom_act n

p2m_export "CerednikDrinfeld.FormalODModule" "nthSeries_isLawHom"
private theorem _root_.CerednikDrinfeld.FormalODModule.act_comm_nthSeries (a : Zp2 q) (n : ℕ) (j : Fin 2) :
    subst (X₀.act a) (X₀.F.nthSeries n j) = subst (X₀.F.nthSeries n) (X₀.act a j) := by
  rw [← X₀.act_natCast]
  show ((X₀.act (n : Zp2 q)).comp (X₀.act a)) j = ((X₀.act a).comp (X₀.act (n : Zp2 q))) j
  rw [← X₀.act_mul, ← X₀.act_mul, mul_comm]

p2m_export "CerednikDrinfeld.FormalODModule" "act_comm_nthSeries"
private theorem _root_.CerednikDrinfeld.FormalODModule.varpi_comm_nthSeries (n : ℕ) (j : Fin 2) :
    subst X₀.varpi (X₀.F.nthSeries n j) = subst (X₀.F.nthSeries n) (X₀.varpi j) := by
  rw [← X₀.act_natCast]
  show ((X₀.act (n : Zp2 q)).comp X₀.varpi) j = (X₀.varpi.comp (X₀.act (n : Zp2 q))) j
  rw [X₀.varpi_comp_act, map_natCast]

p2m_export "CerednikDrinfeld.FormalODModule" "varpi_comm_nthSeries"
end CerednikDrinfeld.FormalODModule

open MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.MvFormalGroup MvFormalGroup.C1Kit in
open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] (X₀ : FormalODModule q k) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    let Θ : MvPowerSeries (Fin 2 ⊕ Fin 2) k → MvPowerSeries (Fin 2) k := fun Γ =>
      ∑ i ∈ Finset.range q,
        MvPowerSeries.subst (Sum.elim (X₀.F.nthSeries i) fun l => MvPowerSeries.X l) Γ
    (∀ (c : k) (Γ Γ' : MvPowerSeries (Fin 2 ⊕ Fin 2) k), Θ (c • Γ + Γ') = c • Θ Γ + Θ Γ') ∧
    (∀ g : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff g = 0 →
      Θ (X₀.F.addCoboundary g) = MvPowerSeries.subst (X₀.F.nthSeries q) g) ∧
    (∀ (a : Zp2 q) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      Θ (pull (X₀.act a) Γ) = MvPowerSeries.subst (X₀.act a) (Θ Γ)) ∧
    (∀ Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, Θ (pull X₀.varpi Γ) = MvPowerSeries.subst X₀.varpi (Θ Γ)) ∧
    (∀ Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k, X₀.F.IsSymmTwoCocycle Γ →
      X₀.F.addCoboundary (Θ Γ) = pull (X₀.F.nthSeries q) Γ) ∧
    (∀ (φ : Fin 2 → MvPowerSeries (Fin 2) k) (Γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k),
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → MvPowerSeries.constantCoeff Γ = 0 →
      pull φ Γ ∈ Ideal.span (Set.range (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))))) := by
  intro pull Θ
  haveI := X₀.isComm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c Γ Γ'
    show ∑ i ∈ Finset.range q, subst _ (c • Γ + Γ') = c • (∑ i ∈ Finset.range q, subst _ Γ) + ∑ i ∈ Finset.range q, subst _ Γ'
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [subst_add (hasSubst_nthPair X₀.F i), subst_smul (hasSubst_nthPair X₀.F i)]
  · intro g₁ hg₁
    show ∑ i ∈ Finset.range q, subst _ (X₀.F.addCoboundary g₁) = _
    rw [theta_addCoboundary X₀.F q g₁ hg₁, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k q, zero_smul, sub_zero]
  · intro a Γ
    show ∑ i ∈ Finset.range q, subst _ (subst (Sum.elim (inL (X₀.act a)) (inR (X₀.act a))) Γ)
      = subst (X₀.act a) (∑ i ∈ Finset.range q, subst _ Γ)
    rw [← coe_substAlgHom (X₀.isLawHom_act a).hasSubst, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_substAlgHom]
    exact (subst_nthPair_comm X₀.F i (X₀.isLawHom_act a).1 (X₀.act_comm_nthSeries a i) Γ).symm
  · intro Γ
    show ∑ i ∈ Finset.range q, subst _ (subst (Sum.elim (inL X₀.varpi) (inR X₀.varpi)) Γ)
      = subst X₀.varpi (∑ i ∈ Finset.range q, subst _ Γ)
    rw [← coe_substAlgHom X₀.isLawHom_varpi.hasSubst, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_substAlgHom]
    exact (subst_nthPair_comm X₀.F i X₀.isLawHom_varpi.1 (X₀.varpi_comm_nthSeries i) Γ).symm
  · intro Γ hΓ
    show X₀.F.addCoboundary (∑ i ∈ Finset.range q, subst _ Γ)
      = subst (Sum.elim (inL (X₀.F.nthSeries q)) (inR (X₀.F.nthSeries q))) Γ
    rw [addCoboundary_theta X₀.F q hΓ (fun n => (X₀.nthSeries_isLawHom n).2), ← Nat.cast_smul_eq_nsmul k,
      CharP.cast_eq_zero k q, zero_smul, sub_zero]
  · intro φ Γ hφ hΓ
    exact subst_mem_span_of_constantCoeff (hasSubst_pull hφ) hΓ

end S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_connectingSum_smul_add_and_addCoboundary_and_subst_act_and_addCoboundary_eq_subst_nthSeries_and_mem_span (solution)
