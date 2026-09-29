-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_mvFormalGroup_isComm_isLawHom_of_invariant_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/842b2afb-4e16-5753-9f41-9325582ed6d8

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_mem_span_image_subst_of_subst_mem_span_image_subst_of_projective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_mvFormalGroup_isComm_isLawHom_of_invariant_coordinates

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff X subst_X)

namespace P2mD2

section Inj

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
  (hdesc : ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w)

noncomputable def uT (n : ℕ) : Fin 2 ⊕ Fin n → MvPowerSeries (Fin 2 ⊕ Fin n) B :=
  Sum.elim
    (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
    (fun t => MvPowerSeries.X (Sum.inr t))

include hu0 in
theorem hasSubst_uT (n : ℕ) : HasSubst (uT u n) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (j | t)
  · show constantCoeff (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j)) = 0
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hu0 j)
  · exact MvPowerSeries.constantCoeff_X _

include hu0 hdesc in

theorem eq_zero_of_subst_uT_eq_zero (n : ℕ) (W : MvPowerSeries (Fin 2 ⊕ Fin n) B)
    (hW : MvPowerSeries.subst (uT u n) W = 0) : W = 0 := by

  have hA : HasSubst (Sum.elim
      (fun j => MvPowerSeries.subst
        (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
          (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
        (X.F.toPowerSeries j))
      (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | t)
    · exact MvPowerSeries.constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _))
        (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _) (X.F.constantCoeff_eq_zero j)
    · exact MvPowerSeries.constantCoeff_X _
  have hB : HasSubst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
      (fun t => MvPowerSeries.X (Sum.inr t))) :=
    hasSubst_of_constantCoeff_zero (by rintro (l | t) <;> exact MvPowerSeries.constantCoeff_X _)
  have h0 := hdesc n 0 (by
    rw [← MvPowerSeries.coe_substAlgHom hA, ← MvPowerSeries.coe_substAlgHom hB, map_zero, map_zero, sub_self]
    exact Ideal.zero_mem _)
  obtain ⟨W₀, hW₀, huniq⟩ := h0
  have h1 : W = W₀ := huniq W hW
  have h2 : (0 : MvPowerSeries (Fin 2 ⊕ Fin n) B) = W₀ := huniq 0 (by
    show MvPowerSeries.subst (uT u n) 0 = 0
    rw [← MvPowerSeries.coe_substAlgHom (hasSubst_uT u hu0 n), map_zero])
  rw [h1, ← h2]

include hu0 hdesc in
theorem subst_uT_injective (n : ℕ) : Function.Injective (MvPowerSeries.subst (R := B) (uT u n)) := by
  intro W W' h
  have h' : MvPowerSeries.subst (uT u n) (W - W') = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom (hasSubst_uT u hu0 n), map_sub, MvPowerSeries.coe_substAlgHom, h, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_subst_uT_eq_zero X I u hu0 hdesc n _ h')

end Inj

end P2mD2

namespace P2mD2
section Gen
variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
  (hdesc : ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w)

omit hu0 hdesc in

theorem rename_subst {σ τ τ' : Type} [Finite σ] [Finite τ] (f : τ → τ') (a : σ → MvPowerSeries τ B)
    (ha : ∀ i, constantCoeff (a i) = 0) (g : MvPowerSeries σ B) :
    MvPowerSeries.rename f (MvPowerSeries.subst a g) = MvPowerSeries.subst (fun i => MvPowerSeries.rename f (a i)) g := by
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (MvPowerSeries.HasSubst.X_comp f)]
  congr 1
  funext i
  rw [MvPowerSeries.rename_eq_subst]

omit hu0 hdesc in
theorem rename_eq_self_of_eq_id {σ : Type} (f : σ → σ) [Filter.TendstoCofinite f] (hf : f = id) (q : MvPowerSeries σ B) :
    MvPowerSeries.rename f q = q := by
  subst hf
  exact MvPowerSeries.rename_id_apply q

end Gen
end P2mD2

namespace P2mD2

section Four

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
  (hdesc : ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w)

noncomputable def uLR : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  Sum.elim
    (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
    (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))

noncomputable def xuR : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
    (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))

omit hdesc in
include hu0 in
theorem hasSubst_uLR : HasSubst (uLR u) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (j | j) <;>
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hu0 j)

omit hdesc in
include hu0 in
theorem hasSubst_xuR : HasSubst (xuR u) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (l | j)
  · exact MvPowerSeries.constantCoeff_X _
  · exact MvPowerSeries.constantCoeff_subst_eq_zero
      (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hu0 j)

omit hdesc in
include hu0 in

theorem subst_uLR_eq (V : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    MvPowerSeries.subst (uLR u) V = MvPowerSeries.subst (xuR u) (MvPowerSeries.subst (uT u 2) V) := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_uT u hu0 2) (hasSubst_xuR u hu0)]
  congr 1
  funext v
  rcases v with j | t
  · show _ = MvPowerSeries.subst (xuR u) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (hasSubst_xuR u hu0)]
    show MvPowerSeries.subst _ (u j) = _
    congr 1
    funext l
    rw [subst_X (hasSubst_xuR u hu0)]
    rfl
  · show MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u t) =
      MvPowerSeries.subst (xuR u) (MvPowerSeries.X (Sum.inr t))
    rw [subst_X (hasSubst_xuR u hu0)]
    rfl

omit hdesc in
include hu0 in

theorem subst_xuR_eq (V : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    MvPowerSeries.subst (xuR u) V =
      MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2)
        (MvPowerSeries.subst (uT u 2) (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) V)) := by
  rw [rename_subst _ _ (fun v => by
        rcases v with j | t
        · exact MvPowerSeries.constantCoeff_subst_eq_zero
            (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hu0 j)
        · exact MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp Sum.swap)
      (hasSubst_of_constantCoeff_zero (fun v => by
        rw [MvPowerSeries.constantCoeff_rename]
        rcases v with j | t
        · exact MvPowerSeries.constantCoeff_subst_eq_zero
            (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hu0 j)
        · exact MvPowerSeries.constantCoeff_X _))]
  have hc : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (uT u 2 s)) = 0 := by
    intro s
    rw [MvPowerSeries.constantCoeff_rename]
    rcases s with j | t
    · exact MvPowerSeries.constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hu0 j)
    · exact MvPowerSeries.constantCoeff_X _
  congr 1
  funext v
  rw [Function.comp_apply, subst_X (hasSubst_of_constantCoeff_zero hc)]
  rcases v with l | j
  · show (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B) = MvPowerSeries.rename Sum.swap (MvPowerSeries.X (Sum.inr l))
    rw [MvPowerSeries.rename_X]
    rfl
  · show MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) =
      MvPowerSeries.rename Sum.swap (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
    rw [rename_subst _ _ (fun _ => MvPowerSeries.constantCoeff_X _)]
    congr 1
    funext l
    rw [MvPowerSeries.rename_X]
    rfl

include hu0 hdesc in

theorem subst_uLR_injective : Function.Injective (MvPowerSeries.subst (R := B) (uLR u)) := by
  have hsw : Function.Injective (MvPowerSeries.rename (R := B) (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2)) :=
    MvPowerSeries.rename_injective (R := B) ⟨Sum.swap, Sum.swap_leftInverse.injective⟩
  intro V V' h
  rw [subst_uLR_eq u hu0, subst_uLR_eq u hu0, subst_xuR_eq u hu0, subst_xuR_eq u hu0] at h
  exact subst_uT_injective X I u hu0 hdesc 2 (hsw (subst_uT_injective X I u hu0 hdesc 2 (hsw h)))

omit hdesc in
include hu0 in

theorem constantCoeff_subst_u (W : MvPowerSeries (Fin 2) B) :
    constantCoeff (MvPowerSeries.subst u W) = constantCoeff W := by
  have hu := hasSubst_of_constantCoeff_zero hu0
  have hW' : constantCoeff (W - MvPowerSeries.C (constantCoeff W)) = 0 := by
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h0 : constantCoeff (MvPowerSeries.subst u (W - MvPowerSeries.C (constantCoeff W))) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hu hu0 hW'
  have hC : MvPowerSeries.substAlgHom (R := B) hu (MvPowerSeries.C (constantCoeff W)) =
      MvPowerSeries.C (σ := Fin 2) (constantCoeff W) := by
    rw [MvPowerSeries.c_eq_algebraMap]
    exact AlgHom.commutes _ _
  have hsplit : MvPowerSeries.subst u W =
      MvPowerSeries.subst u (W - MvPowerSeries.C (constantCoeff W)) + MvPowerSeries.C (constantCoeff W) := by
    rw [← MvPowerSeries.coe_substAlgHom hu, map_sub, hC, sub_add_cancel]
  rw [hsplit, map_add, h0, MvPowerSeries.constantCoeff_C, zero_add]

end Four

end P2mD2

namespace P2mD2

section FG2H

variable {B : Type} [CommRing B]

theorem cc_elim {σ₁ σ₂ τ : Type} {a : σ₁ → MvPowerSeries τ B} {b : σ₂ → MvPowerSeries τ B}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    ∀ s, MvPowerSeries.constantCoeff (Sum.elim a b s) = 0 := by
  rintro (i | i)
  · exact ha i
  · exact hb i

theorem cc_substF {g : ℕ} (F : MvFormalGroup g B) {τ : Type} {a : Fin g ⊕ Fin g → MvPowerSeries τ B}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (j : Fin g) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a (F.toPowerSeries j)) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha (F.constantCoeff_eq_zero j)

theorem law_assoc_subst {g : ℕ} (F : MvFormalGroup g B) {τ : Type}
    (α β γ : Fin g → MvPowerSeries τ B)
    (hα : ∀ j, MvPowerSeries.constantCoeff (α j) = 0) (hβ : ∀ j, MvPowerSeries.constantCoeff (β j) = 0)
    (hγ : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0) (k : Fin g) :
    MvPowerSeries.subst (Sum.elim (fun j => MvPowerSeries.subst (Sum.elim α β) (F.toPowerSeries j)) γ) (F.toPowerSeries k) =
      MvPowerSeries.subst (Sum.elim α fun j => MvPowerSeries.subst (Sum.elim β γ) (F.toPowerSeries j)) (F.toPowerSeries k) := by
  have hΦ : HasSubst (Sum.elim α (Sum.elim β γ)) := hasSubst_of_constantCoeff_zero (cc_elim hα (cc_elim hβ hγ))
  have hXL : ∀ s, MvPowerSeries.constantCoeff (Sum.elim
      (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B))
      (fun l => MvPowerSeries.X (Sum.inr (Sum.inl l))) s) = 0 :=
    cc_elim (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _)
  have hXR : ∀ s, MvPowerSeries.constantCoeff (Sum.elim
      (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B))
      (fun l => MvPowerSeries.X (Sum.inr (Sum.inr l))) s) = 0 :=
    cc_elim (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _)
  have hL : HasSubst (Sum.elim
      (fun j => MvPowerSeries.subst
        (Sum.elim
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B))
          fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))
        (F.toPowerSeries j))
      fun j => (MvPowerSeries.X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B)) :=
    hasSubst_of_constantCoeff_zero (cc_elim (cc_substF F hXL) (fun _ => MvPowerSeries.constantCoeff_X _))
  have hR : HasSubst (Sum.elim
      (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B))
      fun j => MvPowerSeries.subst
        (Sum.elim
          (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B))
          fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))
        (F.toPowerSeries j)) :=
    hasSubst_of_constantCoeff_zero (cc_elim (fun _ => MvPowerSeries.constantCoeff_X _) (cc_substF F hXR))
  have h := congrArg (MvPowerSeries.subst (Sum.elim α (Sum.elim β γ))) (F.assoc k)
  rw [MvPowerSeries.subst_comp_subst_apply hL hΦ, MvPowerSeries.subst_comp_subst_apply hR hΦ] at h
  have e1 : (fun s => MvPowerSeries.subst (Sum.elim α (Sum.elim β γ)) (Sum.elim
      (fun j => MvPowerSeries.subst
        (Sum.elim
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B))
          fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))
        (F.toPowerSeries j))
      (fun j => (MvPowerSeries.X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B)) s)) =
      Sum.elim (fun j => MvPowerSeries.subst (Sum.elim α β) (F.toPowerSeries j)) γ := by
    funext s
    rcases s with j | j
    · simp only [Sum.elim_inl]
      rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hXL) hΦ]
      congr 1
      funext l
      rcases l with l | l <;> simp only [Sum.elim_inl, Sum.elim_inr, subst_X hΦ]
    · simp only [Sum.elim_inr, subst_X hΦ]
  have e2 : (fun s => MvPowerSeries.subst (Sum.elim α (Sum.elim β γ)) (Sum.elim
      (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B))
      (fun j => MvPowerSeries.subst
        (Sum.elim
          (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) B))
          fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))
        (F.toPowerSeries j)) s)) =
      Sum.elim α (fun j => MvPowerSeries.subst (Sum.elim β γ) (F.toPowerSeries j)) := by
    funext s
    rcases s with j | j
    · simp only [Sum.elim_inl, subst_X hΦ]
    · simp only [Sum.elim_inr]
      rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hXR) hΦ]
      congr 1
      funext l
      rcases l with l | l <;> simp only [Sum.elim_inl, Sum.elim_inr, subst_X hΦ]
  rw [e1, e2] at h
  exact h

theorem law_comm_subst {g : ℕ} (F : MvFormalGroup g B) [F.IsComm] {τ : Type}
    (α β : Fin g → MvPowerSeries τ B)
    (hα : ∀ j, MvPowerSeries.constantCoeff (α j) = 0) (hβ : ∀ j, MvPowerSeries.constantCoeff (β j) = 0) (k : Fin g) :
    MvPowerSeries.subst (Sum.elim β α) (F.toPowerSeries k) = MvPowerSeries.subst (Sum.elim α β) (F.toPowerSeries k) := by
  have hΦ : HasSubst (Sum.elim α β) := hasSubst_of_constantCoeff_zero (cc_elim hα hβ)
  have hS : HasSubst (Sum.elim
      (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) B))
      fun j => MvPowerSeries.X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (cc_elim (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _))
  have h := congrArg (MvPowerSeries.subst (Sum.elim α β)) (MvFormalGroup.IsComm.comm (F := F) k)
  rw [MvPowerSeries.subst_comp_subst_apply hS hΦ] at h
  have e1 : (fun s => MvPowerSeries.subst (Sum.elim α β) (Sum.elim
      (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) B))
      (fun j => MvPowerSeries.X (Sum.inl j)) s)) = Sum.elim β α := by
    funext s
    rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, subst_X hΦ]
  rw [e1] at h
  exact h

theorem subst_elim_subst_law {g : ℕ} (F : MvFormalGroup g B) {τ : Type}
    (α β : Fin g → MvPowerSeries τ B)
    (hα : ∀ j, MvPowerSeries.constantCoeff (α j) = 0) (hβ : ∀ j, MvPowerSeries.constantCoeff (β j) = 0)
    (v : MvPowerSeries (Fin g) B) :
    MvPowerSeries.subst (Sum.elim α β) (MvPowerSeries.subst F.toPowerSeries v) =
      MvPowerSeries.subst (fun j => MvPowerSeries.subst (Sum.elim α β) (F.toPowerSeries j)) v :=
  MvPowerSeries.subst_comp_subst_apply F.hasSubst_toPowerSeries (hasSubst_of_constantCoeff_zero (cc_elim hα hβ)) v

theorem inv_transport {g : ℕ} (F : MvFormalGroup g B) (I : Ideal (MvPowerSeries (Fin g) B))
    (f : MvPowerSeries (Fin g) B)
    (hf : MvPowerSeries.subst F.toPowerSeries f -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) B)) f ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) B))) ''
        (I : Set (MvPowerSeries (Fin g) B))))
    {τ : Type} (a : Fin g → MvPowerSeries τ B) (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (κ : Fin g → τ) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst (Sum.elim a (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B)))
        (F.toPowerSeries j)) f -
      MvPowerSeries.subst a f ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B))) ''
        (I : Set (MvPowerSeries (Fin g) B))) := by
  have hκ : ∀ l, MvPowerSeries.constantCoeff ((fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B)) l) = 0 :=
    fun _ => MvPowerSeries.constantCoeff_X _
  have hφ : HasSubst (Sum.elim a (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B))) :=
    hasSubst_of_constantCoeff_zero (cc_elim ha hκ)
  have hXl : HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) B)) :=
    hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  have hXr : HasSubst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) B)) :=
    hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  have h1 : MvPowerSeries.subst (Sum.elim a (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B)))
      (MvPowerSeries.subst F.toPowerSeries f) =
      MvPowerSeries.subst (fun j => MvPowerSeries.subst (Sum.elim a (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B)))
        (F.toPowerSeries j)) f :=
    MvPowerSeries.subst_comp_subst_apply F.hasSubst_toPowerSeries hφ f
  have h2 : MvPowerSeries.subst (Sum.elim a (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B)))
      (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) B)) f) =
      MvPowerSeries.subst a f := by
    rw [MvPowerSeries.subst_comp_subst_apply hXl hφ]
    congr 1
    funext l
    rw [subst_X hφ, Sum.elim_inl]
  have hle : Ideal.map (MvPowerSeries.substAlgHom hφ)
      (Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) B))) ''
        (I : Set (MvPowerSeries (Fin g) B)))) ≤
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B))) ''
        (I : Set (MvPowerSeries (Fin g) B))) := by
    rw [Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    apply Ideal.subset_span
    refine ⟨i, hi, ?_⟩
    show MvPowerSeries.subst (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B)) i =
      MvPowerSeries.substAlgHom hφ
        (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) B)) i)
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_comp_subst_apply hXr hφ]
    congr 1
    funext l
    rw [subst_X hφ, Sum.elim_inr]
  rw [← h1, ← h2, ← MvPowerSeries.subst_sub hφ, ← MvPowerSeries.substAlgHom_apply hφ]
  exact hle (Ideal.mem_map_of_mem (MvPowerSeries.substAlgHom hφ) hf)

theorem subst_elim_rename_swap {σ₁ σ₂ τ : Type} [Finite σ₁] [Finite σ₂]
    (a : σ₁ → MvPowerSeries τ B) (b : σ₂ → MvPowerSeries τ B)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (W : MvPowerSeries (σ₂ ⊕ σ₁) B) :
    MvPowerSeries.subst (Sum.elim a b) (MvPowerSeries.rename (Sum.swap : σ₂ ⊕ σ₁ → σ₁ ⊕ σ₂) W) =
      MvPowerSeries.subst (Sum.elim b a) W := by
  have hab : HasSubst (Sum.elim a b) := hasSubst_of_constantCoeff_zero (cc_elim ha hb)
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hab]
  congr 1
  funext s
  rcases s with i | i <;>
    simp only [Function.comp_apply, Sum.swap_inl, Sum.swap_inr, subst_X hab, Sum.elim_inl, Sum.elim_inr]

theorem uT_def {u : Series B} (n : ℕ) : uT u n =
    Sum.elim
      (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
      (fun t => MvPowerSeries.X (Sum.inr t)) := rfl

theorem subst_elim_substu (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) (n : ℕ) {τ : Type}
    (α : Fin 2 → MvPowerSeries τ B) (β : Fin n → MvPowerSeries τ B)
    (hα : ∀ j, MvPowerSeries.constantCoeff (α j) = 0) (hβ : ∀ j, MvPowerSeries.constantCoeff (β j) = 0)
    (W : MvPowerSeries (Fin 2 ⊕ Fin n) B) :
    MvPowerSeries.subst (Sum.elim (fun j => MvPowerSeries.subst α (u j)) β) W =
      MvPowerSeries.subst (Sum.elim α β) (MvPowerSeries.subst (uT u n) W) := by
  have hχ : HasSubst (Sum.elim α β) := hasSubst_of_constantCoeff_zero (cc_elim hα hβ)
  have hXl : HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) :=
    hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_uT u hu0 n) hχ, uT_def]
  congr 1
  funext s
  rcases s with j | t
  · simp only [Sum.elim_inl]
    rw [MvPowerSeries.subst_comp_subst_apply hXl hχ]
    congr 1
    funext l
    rw [subst_X hχ, Sum.elim_inl]
  · simp only [Sum.elim_inr, subst_X hχ]

end FG2H

end P2mD2

namespace P2mD2

section ToolsDE

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
  (hdesc : ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w)

omit hdesc in
include hu0 in
theorem constantCoeff_uLR : ∀ s, constantCoeff (uLR u s) = 0 := by
  rintro (j | j) <;>
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hu0 j)

omit hdesc in
include hu0 in

theorem subst_uLR_eq' (V : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    MvPowerSeries.subst (uLR u) V = MvPowerSeries.subst (uT u 2) (MvPowerSeries.subst (xuR u) V) := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_xuR u hu0) (hasSubst_uT u hu0 2)]
  congr 1
  funext v
  rcases v with l | j
  · show MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u l) =
      MvPowerSeries.subst (uT u 2) (MvPowerSeries.X (Sum.inl l))
    rw [subst_X (hasSubst_uT u hu0 2)]
    rfl
  · show MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) =
      MvPowerSeries.subst (uT u 2) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (hasSubst_uT u hu0 2)]
    congr 1
    funext l
    rw [subst_X (hasSubst_uT u hu0 2)]
    rfl

omit hu0 hdesc in

theorem rename_swap_swap (V : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2)
      (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) V) = V := by
  rw [MvPowerSeries.rename_rename]
  exact rename_eq_self_of_eq_id _ Sum.swap_swap_eq V

omit hdesc in
include hu0 in

theorem subst_uLR_rename_swap (V : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    MvPowerSeries.subst (uLR u) (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) V) =
      MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (MvPowerSeries.subst (uLR u) V) := by
  rw [rename_subst _ _ (constantCoeff_uLR u hu0), MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) (hasSubst_uLR u hu0)]
  congr 1
  funext v
  rw [Function.comp_apply, subst_X (hasSubst_uLR u hu0)]
  rcases v with j | j
  · show MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) =
      MvPowerSeries.rename Sum.swap (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
    rw [rename_subst _ _ (fun _ => MvPowerSeries.constantCoeff_X _)]
    congr 1
    funext l
    rw [MvPowerSeries.rename_X]
    rfl
  · show MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) =
      MvPowerSeries.rename Sum.swap (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
    rw [rename_subst _ _ (fun _ => MvPowerSeries.constantCoeff_X _)]
    congr 1
    funext l
    rw [MvPowerSeries.rename_X]
    rfl

omit hu0 hdesc in

theorem constantCoeff_subst_of_constantCoeff_zero {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ B)
    (ha : ∀ s, constantCoeff (a s) = 0) (W : MvPowerSeries σ B) :
    constantCoeff (MvPowerSeries.subst a W) = constantCoeff W := by
  have hA := hasSubst_of_constantCoeff_zero ha
  have hW' : constantCoeff (W - MvPowerSeries.C (constantCoeff W)) = 0 := by
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h0 : constantCoeff (MvPowerSeries.subst a (W - MvPowerSeries.C (constantCoeff W))) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hA ha hW'
  have hC : MvPowerSeries.substAlgHom (R := B) hA (MvPowerSeries.C (constantCoeff W)) =
      MvPowerSeries.C (σ := τ) (constantCoeff W) := by
    rw [MvPowerSeries.c_eq_algebraMap, MvPowerSeries.c_eq_algebraMap]
    exact AlgHom.commutes _ _
  have hsplit : MvPowerSeries.subst a W =
      MvPowerSeries.subst a (W - MvPowerSeries.C (constantCoeff W)) + MvPowerSeries.C (constantCoeff W) := by
    rw [← MvPowerSeries.coe_substAlgHom hA, map_sub, hC, sub_add_cancel]
  rw [hsplit, map_add, h0, MvPowerSeries.constantCoeff_C, zero_add]

include hu0 hdesc in

theorem subst_block_injective {σ : Type} [Finite σ] (n : ℕ) (ε : σ ≃ Fin 2 ⊕ Fin n)
    (a : σ → MvPowerSeries σ B) (ha : ∀ s, constantCoeff (a s) = 0)
    (hε : ∀ s, MvPowerSeries.rename ε (a s) = uT u n (ε s)) :
    Function.Injective (MvPowerSeries.subst (R := B) a) := by
  have hρ : Function.Injective (MvPowerSeries.rename (R := B) (ε : σ → Fin 2 ⊕ Fin n)) :=
    MvPowerSeries.rename_injective (R := B) ε.toEmbedding
  have hL : ∀ W : MvPowerSeries σ B, MvPowerSeries.rename ε (MvPowerSeries.subst a W) =
      MvPowerSeries.subst (fun s => MvPowerSeries.rename ε (a s)) W :=
    fun W => rename_subst _ a ha W
  have hR : ∀ W : MvPowerSeries σ B, MvPowerSeries.subst (uT u n) (MvPowerSeries.rename ε W) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst (uT u n) (MvPowerSeries.X (ε s) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) W := by
    intro W
    rw [MvPowerSeries.rename_eq_subst,
      MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) (hasSubst_uT u hu0 n)]
    rfl
  have hcomm : ∀ W : MvPowerSeries σ B, MvPowerSeries.rename ε (MvPowerSeries.subst a W) =
      MvPowerSeries.subst (uT u n) (MvPowerSeries.rename ε W) := by
    intro W
    rw [hL, hR]
    congr 1
    funext s
    rw [hε s, subst_X (hasSubst_uT u hu0 n)]
  intro W W' h
  apply hρ
  apply subst_uT_injective X I u hu0 hdesc n
  rw [← hcomm, ← hcomm, h]

noncomputable abbrev ren₀ : MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2 ⊕ Fin 0) B :=
  MvPowerSeries.rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 0)

omit hu0 hdesc in
theorem ren₀_injective : Function.Injective (ren₀ (B := B)) :=
  MvPowerSeries.rename_injective (R := B) ⟨Sum.inl, Sum.inl_injective⟩

omit hdesc in
include hu0 in

theorem ren₀_subst_u (V : MvPowerSeries (Fin 2) B) :
    ren₀ (MvPowerSeries.subst u V) = MvPowerSeries.subst (uT u 0) (ren₀ V) := by
  rw [rename_subst _ u hu0]
  show _ = MvPowerSeries.subst (uT u 0) (MvPowerSeries.rename Sum.inl V)
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp Sum.inl) (hasSubst_uT u hu0 0)]
  congr 1
  funext j
  show MvPowerSeries.rename Sum.inl (u j) = MvPowerSeries.subst (uT u 0) (MvPowerSeries.X (Sum.inl j))
  rw [subst_X (hasSubst_uT u hu0 0), MvPowerSeries.rename_eq_subst]
  rfl

include hu0 hdesc in

theorem subst_u_injective : Function.Injective (MvPowerSeries.subst (R := B) u) := by
  intro V V' h
  apply ren₀_injective
  apply subst_uT_injective X I u hu0 hdesc 0
  rw [← ren₀_subst_u u hu0, ← ren₀_subst_u u hu0, h]

end ToolsDE

end P2mD2

namespace P2mD2

section FG2I

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
  (hdesc : ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w)

noncomputable def uTτ (τ : Type) : Fin 2 ⊕ τ → MvPowerSeries (Fin 2 ⊕ τ) B :=
  Sum.elim
    (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ τ) B)) (u j))
    (fun t => MvPowerSeries.X (Sum.inr t))

theorem uTτ_def (τ : Type) : uTτ u τ =
    Sum.elim
      (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ τ) B)) (u j))
      (fun t => MvPowerSeries.X (Sum.inr t)) := rfl

theorem uLR_def : uLR u =
    Sum.elim
      (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
      (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j)) := rfl

omit X I hdesc in
include hu0 in
theorem cc_substu {τ : Type} [Finite τ] (κ : Fin 2 → τ) (j : Fin 2) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst (fun l => (MvPowerSeries.X (κ l) : MvPowerSeries τ B)) (u j)) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hu0 j)

include hu0 in
theorem cc_uTτ (τ : Type) [Finite τ] : ∀ s, MvPowerSeries.constantCoeff (uTτ u τ s) = 0 := by
  rintro (j | t)
  · exact cc_substu u hu0 (τ := Fin 2 ⊕ τ) Sum.inl j
  · exact MvPowerSeries.constantCoeff_X _

include hu0 in
theorem hasSubst_uTτ (τ : Type) [Finite τ] : HasSubst (uTτ u τ) :=
  hasSubst_of_constantCoeff_zero (cc_uTτ u hu0 τ)

include hu0 hdesc in

theorem subst_uTτ_injective (τ : Type) [Fintype τ] :
    Function.Injective (MvPowerSeries.subst (R := B) (uTτ u τ)) := by
  let n : ℕ := Fintype.card τ
  let e : τ ≃ Fin n := Fintype.equivFin τ
  let m : Fin 2 ⊕ τ → Fin 2 ⊕ Fin n := Sum.map id e
  have hm : Function.Injective m := Sum.map_injective.mpr ⟨Function.injective_id, e.injective⟩
  have hR : Function.Injective (MvPowerSeries.rename (R := B) m) := MvPowerSeries.rename_injective (R := B) ⟨m, hm⟩
  have hXl : ∀ l, MvPowerSeries.constantCoeff ((fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ τ) B)) l) = 0 :=
    fun _ => MvPowerSeries.constantCoeff_X _
  have conj : ∀ W : MvPowerSeries (Fin 2 ⊕ τ) B,
      MvPowerSeries.rename m (MvPowerSeries.subst (uTτ u τ) W) = MvPowerSeries.subst (uT u n) (MvPowerSeries.rename m W) := by
    intro W
    rw [rename_subst m _ (cc_uTτ u hu0 τ), MvPowerSeries.rename_eq_subst (f := m) (p := W),
      MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp m) (hasSubst_uT u hu0 n)]
    congr 1
    funext s
    rcases s with j | t
    · simp only [uTτ_def, Sum.elim_inl, Function.comp_apply, subst_X (hasSubst_uT u hu0 n)]
      rw [rename_subst m _ hXl]
      simp only [MvPowerSeries.rename_X, uT_def, m, Sum.map_inl, id_eq, Sum.elim_inl]
    · simp only [uTτ_def, Sum.elim_inr, Function.comp_apply, subst_X (hasSubst_uT u hu0 n), MvPowerSeries.rename_X]
      simp only [uT_def, m, Sum.map_inr, Sum.elim_inr]
  intro W W' h
  apply hR
  apply subst_uT_injective X I u hu0 hdesc n
  rw [← conj, ← conj, h]

def m₂ : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) → Fin 2 ⊕ (Fin 2 ⊕ Fin 2) :=
  Sum.elim (fun a => Sum.inr (Sum.inl a)) (Sum.elim (fun b => Sum.inl b) (fun c => Sum.inr (Sum.inr c)))

def m₃ : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) → Fin 2 ⊕ (Fin 2 ⊕ Fin 2) :=
  Sum.elim (fun a => Sum.inr (Sum.inr a)) (Sum.elim (fun b => Sum.inr (Sum.inl b)) (fun c => Sum.inl c))

theorem m₂_injective : Function.Injective m₂ :=
  Function.LeftInverse.injective (g := m₂) (by rintro (a | b | c) <;> rfl)

theorem m₃_injective : Function.Injective m₃ :=
  Function.LeftInverse.injective (g := m₃) (by rintro (a | b | c) <;> rfl)

noncomputable def T₂ : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) → MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B :=
  Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)))

noncomputable def T₃ : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) → MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B :=
  Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j)))

noncomputable def T : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) → MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B :=
  Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j))
    (Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j)) (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j)))

theorem T₂_def : T₂ u = Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) := rfl
theorem T₃_def : T₃ u = Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j))) := rfl
theorem T_def : T u = Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j))
    (Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j)) (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j))) := rfl

include hu0 in
theorem cc_T₂ : ∀ s, MvPowerSeries.constantCoeff (T₂ u s) = 0 :=
  cc_elim (fun _ => MvPowerSeries.constantCoeff_X _)
    (cc_elim (cc_substu u hu0 (τ := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (fun l => Sum.inr (Sum.inl l)))
      (fun _ => MvPowerSeries.constantCoeff_X _))

include hu0 in
theorem cc_T₃ : ∀ s, MvPowerSeries.constantCoeff (T₃ u s) = 0 :=
  cc_elim (fun _ => MvPowerSeries.constantCoeff_X _)
    (cc_elim (fun _ => MvPowerSeries.constantCoeff_X _)
      (cc_substu u hu0 (τ := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (fun l => Sum.inr (Sum.inr l))))

include hu0 in
theorem cc_T : ∀ s, MvPowerSeries.constantCoeff (T u s) = 0 :=
  cc_elim (cc_substu u hu0 (τ := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) Sum.inl)
    (cc_elim (cc_substu u hu0 (τ := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (fun l => Sum.inr (Sum.inl l)))
      (cc_substu u hu0 (τ := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (fun l => Sum.inr (Sum.inr l))))

include hu0 in

theorem rename_m₂_subst_T₂ (W : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B) :
    MvPowerSeries.rename m₂ (MvPowerSeries.subst (T₂ u) W) =
      MvPowerSeries.subst (uTτ u (Fin 2 ⊕ Fin 2)) (MvPowerSeries.rename m₂ W) := by
  have hU := hasSubst_uTτ u hu0 (Fin 2 ⊕ Fin 2)
  rw [rename_subst m₂ _ (cc_T₂ u hu0), MvPowerSeries.rename_eq_subst (f := m₂) (p := W),
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp m₂) hU]
  congr 1
  funext s
  rcases s with a | b | c
  · simp only [T₂_def, Sum.elim_inl, Function.comp_apply, subst_X hU, MvPowerSeries.rename_X]
    simp only [m₂, uTτ_def, Sum.elim_inl, Sum.elim_inr]
  · simp only [T₂_def, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, subst_X hU]
    rw [rename_subst m₂ _ (fun _ => MvPowerSeries.constantCoeff_X _)]
    simp only [MvPowerSeries.rename_X, m₂, uTτ_def, Sum.elim_inl, Sum.elim_inr]
  · simp only [T₂_def, Sum.elim_inr, Function.comp_apply, subst_X hU, MvPowerSeries.rename_X]
    simp only [m₂, uTτ_def, Sum.elim_inl, Sum.elim_inr]

include hu0 in
theorem rename_m₃_subst_T₃ (W : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B) :
    MvPowerSeries.rename m₃ (MvPowerSeries.subst (T₃ u) W) =
      MvPowerSeries.subst (uTτ u (Fin 2 ⊕ Fin 2)) (MvPowerSeries.rename m₃ W) := by
  have hU := hasSubst_uTτ u hu0 (Fin 2 ⊕ Fin 2)
  rw [rename_subst m₃ _ (cc_T₃ u hu0), MvPowerSeries.rename_eq_subst (f := m₃) (p := W),
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp m₃) hU]
  congr 1
  funext s
  rcases s with a | b | c
  · simp only [T₃_def, Sum.elim_inl, Function.comp_apply, subst_X hU, MvPowerSeries.rename_X]
    simp only [m₃, uTτ_def, Sum.elim_inl, Sum.elim_inr]
  · simp only [T₃_def, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, subst_X hU, MvPowerSeries.rename_X]
    simp only [m₃, uTτ_def, Sum.elim_inl, Sum.elim_inr]
  · simp only [T₃_def, Sum.elim_inr, Function.comp_apply, subst_X hU]
    rw [rename_subst m₃ _ (fun _ => MvPowerSeries.constantCoeff_X _)]
    simp only [MvPowerSeries.rename_X, m₃, uTτ_def, Sum.elim_inl, Sum.elim_inr]

include hu0 hdesc in
theorem subst_T₂_injective : Function.Injective (MvPowerSeries.subst (R := B) (T₂ u)) := by
  have hR : Function.Injective (MvPowerSeries.rename (R := B) m₂) :=
    MvPowerSeries.rename_injective (R := B) ⟨m₂, m₂_injective⟩
  intro W W' h
  apply hR
  apply subst_uTτ_injective X I u hu0 hdesc (Fin 2 ⊕ Fin 2)
  rw [← rename_m₂_subst_T₂ u hu0, ← rename_m₂_subst_T₂ u hu0, h]

include hu0 hdesc in
theorem subst_T₃_injective : Function.Injective (MvPowerSeries.subst (R := B) (T₃ u)) := by
  have hR : Function.Injective (MvPowerSeries.rename (R := B) m₃) :=
    MvPowerSeries.rename_injective (R := B) ⟨m₃, m₃_injective⟩
  intro W W' h
  apply hR
  apply subst_uTτ_injective X I u hu0 hdesc (Fin 2 ⊕ Fin 2)
  rw [← rename_m₃_subst_T₃ u hu0, ← rename_m₃_subst_T₃ u hu0, h]

include hu0 in

theorem subst_T_eq (W : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B) :
    MvPowerSeries.subst (T u) W =
      MvPowerSeries.subst (uTτ u (Fin 2 ⊕ Fin 2)) (MvPowerSeries.subst (T₂ u) (MvPowerSeries.subst (T₃ u) W)) := by
  have hU := hasSubst_uTτ u hu0 (Fin 2 ⊕ Fin 2)
  have h2 : HasSubst (T₂ u) := hasSubst_of_constantCoeff_zero (cc_T₂ u hu0)
  have h3 : HasSubst (T₃ u) := hasSubst_of_constantCoeff_zero (cc_T₃ u hu0)
  have hvy : HasSubst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) := hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  have hvz : HasSubst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) := hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)

  have e12 : (fun s => MvPowerSeries.subst (uTτ u (Fin 2 ⊕ Fin 2)) (T₂ u s)) =
      Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j))
        (Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) := by
    funext s
    rcases s with a | b | c
    · simp only [T₂_def, Sum.elim_inl, subst_X hU]
      simp only [uTτ_def, Sum.elim_inl]
    · simp only [T₂_def, Sum.elim_inl, Sum.elim_inr]
      rw [MvPowerSeries.subst_comp_subst_apply hvy hU]
      congr 1
      funext l
      simp only [subst_X hU]
      simp only [uTτ_def, Sum.elim_inr]
    · simp only [T₂_def, Sum.elim_inl, Sum.elim_inr, subst_X hU]
      simp only [uTτ_def, Sum.elim_inr]
  have h12 : HasSubst (Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j))
      (Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u j)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)))) :=
    hasSubst_of_constantCoeff_zero (cc_elim (cc_substu u hu0 (τ := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) Sum.inl)
      (cc_elim (cc_substu u hu0 (τ := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (fun l => Sum.inr (Sum.inl l)))
        (fun _ => MvPowerSeries.constantCoeff_X _)))
  rw [MvPowerSeries.subst_comp_subst_apply h2 hU, e12, MvPowerSeries.subst_comp_subst_apply h3 h12, T_def]
  congr 1
  funext s
  rcases s with a | b | c
  · simp only [T₃_def, Sum.elim_inl, subst_X h12]
  · simp only [T₃_def, Sum.elim_inl, Sum.elim_inr, subst_X h12]
  · simp only [T₃_def, Sum.elim_inl, Sum.elim_inr]
    rw [MvPowerSeries.subst_comp_subst_apply hvz h12]
    congr 1
    funext l
    simp only [subst_X h12, Sum.elim_inr]

include hu0 hdesc in

theorem subst_T_injective : Function.Injective (MvPowerSeries.subst (R := B) (T u)) := by
  intro W W' h
  rw [subst_T_eq u hu0, subst_T_eq u hu0] at h
  exact subst_T₃_injective X I u hu0 hdesc (subst_T₂_injective X I u hu0 hdesc (subst_uTτ_injective X I u hu0 hdesc _ h))

end FG2I

end P2mD2

namespace P2mD2

section LawDescent

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
  (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
  (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
  (huinv : ∀ j, MvPowerSeries.subst X.F.toPowerSeries (u j) -
      MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) ∈
    Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
      (I : Set (MvPowerSeries (Fin 2) B))))
  (hdesc : ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w)

def InvN (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B) : Prop :=
  MvPowerSeries.subst
      (Sum.elim
        (fun j => MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
          (X.F.toPowerSeries j))
        (fun t => MvPowerSeries.X (Sum.inr t))) w -
    MvPowerSeries.subst
      (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
        (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
    Ideal.span ((MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B)))

noncomputable def w (i : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) B := MvPowerSeries.subst X.F.toPowerSeries (u i)

include hfin hproj hu0 huinv hdesc

theorem invN_w (i : Fin 2) : InvN X I 2 (w X u i) := by

  let xv : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B := fun l => MvPowerSeries.X (Sum.inl (Sum.inl l))
  let zv : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B := fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))
  let yv : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B := fun t => MvPowerSeries.X (Sum.inr t)
  have hx : ∀ l, MvPowerSeries.constantCoeff (xv l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hz : ∀ l, MvPowerSeries.constantCoeff (zv l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hy : ∀ l, MvPowerSeries.constantCoeff (yv l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hFxz : ∀ j, MvPowerSeries.constantCoeff (MvPowerSeries.subst (Sum.elim xv zv) (X.F.toPowerSeries j)) = 0 :=
    cc_substF X.F (cc_elim hx hz)
  have hFxy : ∀ j, MvPowerSeries.constantCoeff (MvPowerSeries.subst (Sum.elim xv yv) (X.F.toPowerSeries j)) = 0 :=
    cc_substF X.F (cc_elim hx hy)
  unfold InvN w
  change MvPowerSeries.subst (Sum.elim (fun j => MvPowerSeries.subst (Sum.elim xv zv) (X.F.toPowerSeries j)) yv)
        (MvPowerSeries.subst X.F.toPowerSeries (u i)) -
      MvPowerSeries.subst (Sum.elim xv yv) (MvPowerSeries.subst X.F.toPowerSeries (u i)) ∈
      Ideal.span ((MvPowerSeries.subst zv) '' (I : Set (MvPowerSeries (Fin 2) B)))
  rw [subst_elim_subst_law X.F _ yv hFxz hy, subst_elim_subst_law X.F xv yv hx hy]

  have key : (fun j => MvPowerSeries.subst
      (Sum.elim (fun j => MvPowerSeries.subst (Sum.elim xv zv) (X.F.toPowerSeries j)) yv) (X.F.toPowerSeries j)) =
      fun j => MvPowerSeries.subst
        (Sum.elim (fun j => MvPowerSeries.subst (Sum.elim xv yv) (X.F.toPowerSeries j)) zv) (X.F.toPowerSeries j) := by
    funext j
    have hc : (fun j' => MvPowerSeries.subst (Sum.elim zv yv) (X.F.toPowerSeries j')) =
        fun j' => MvPowerSeries.subst (Sum.elim yv zv) (X.F.toPowerSeries j') :=
      funext fun j' => law_comm_subst X.F yv zv hy hz j'
    rw [law_assoc_subst X.F xv zv yv hx hz hy, law_assoc_subst X.F xv yv zv hx hy hz, hc]
  rw [key]
  exact inv_transport X.F I (u i) (huinv i) _ hFxy (fun l => Sum.inl (Sum.inr l))

noncomputable def W₁ (i : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  (hdesc 2 (w X u i) (invN_w X I hfin hproj u hu0 huinv hdesc i)).choose

theorem subst_uT_W₁ (i : Fin 2) : MvPowerSeries.subst (uT u 2) (W₁ X I hfin hproj u hu0 huinv hdesc i) = w X u i :=
  (hdesc 2 (w X u i) (invN_w X I hfin hproj u hu0 huinv hdesc i)).choose_spec.1

theorem invN_W₁_swap (i : Fin 2) :
    InvN X I 2 (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (W₁ X I hfin hproj u hu0 huinv hdesc i)) := by

  let yv : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B := fun l => MvPowerSeries.X (Sum.inl (Sum.inl l))
  let zv : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B := fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))
  let sv : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B := fun t => MvPowerSeries.X (Sum.inr t)
  let ux : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B := fun k => MvPowerSeries.subst sv (u k)
  let Fyz : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B :=
    fun j => MvPowerSeries.subst (Sum.elim yv zv) (X.F.toPowerSeries j)
  let Fxy : Fin 2 → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B :=
    fun j => MvPowerSeries.subst (Sum.elim sv yv) (X.F.toPowerSeries j)
  have hy : ∀ l, MvPowerSeries.constantCoeff (yv l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hz : ∀ l, MvPowerSeries.constantCoeff (zv l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hs : ∀ l, MvPowerSeries.constantCoeff (sv l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hux : ∀ k, MvPowerSeries.constantCoeff (ux k) = 0 := fun k =>
    MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hu0 k)
  have hFyz : ∀ j, MvPowerSeries.constantCoeff (Fyz j) = 0 := cc_substF X.F (cc_elim hy hz)
  have hFxy : ∀ j, MvPowerSeries.constantCoeff (Fxy j) = 0 := cc_substF X.F (cc_elim hs hy)
  have hψ : HasSubst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B)) ux) :=
    hasSubst_of_constantCoeff_zero (cc_elim (fun _ => MvPowerSeries.constantCoeff_X _) hux)
  have hA : HasSubst (Sum.elim Fyz sv) := hasSubst_of_constantCoeff_zero (cc_elim hFyz hs)
  have hB : HasSubst (Sum.elim yv sv) := hasSubst_of_constantCoeff_zero (cc_elim hy hs)
  have hyz : HasSubst (Sum.elim yv zv) := hasSubst_of_constantCoeff_zero (cc_elim hy hz)
  unfold InvN
  change MvPowerSeries.subst (Sum.elim Fyz sv)
        (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (W₁ X I hfin hproj u hu0 huinv hdesc i)) -
      MvPowerSeries.subst (Sum.elim yv sv)
        (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (W₁ X I hfin hproj u hu0 huinv hdesc i)) ∈
      Ideal.span ((MvPowerSeries.subst zv) '' (I : Set (MvPowerSeries (Fin 2) B)))
  refine MvPowerSeries.mem_span_image_subst_of_subst_mem_span_image_subst_of_projective I hfin hproj u hu0
    (fun H hH => eq_zero_of_subst_uT_eq_zero X I u hu0 hdesc 2 H (by rw [uT_def]; exact hH)) _ ?_
  change MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B)) ux)
      (MvPowerSeries.subst (Sum.elim Fyz sv)
          (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (W₁ X I hfin hproj u hu0 huinv hdesc i)) -
        MvPowerSeries.subst (Sum.elim yv sv)
          (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (W₁ X I hfin hproj u hu0 huinv hdesc i))) ∈
      Ideal.span ((MvPowerSeries.subst zv) '' (I : Set (MvPowerSeries (Fin 2) B)))
  rw [MvPowerSeries.subst_sub hψ, MvPowerSeries.subst_comp_subst_apply hA hψ, MvPowerSeries.subst_comp_subst_apply hB hψ]

  have e1 : (fun s => MvPowerSeries.subst
      (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B)) ux)
      (Sum.elim Fyz sv s)) = Sum.elim Fyz ux := by
    funext s
    rcases s with j | t
    · simp only [Sum.elim_inl]
      show MvPowerSeries.subst _ (MvPowerSeries.subst (Sum.elim yv zv) (X.F.toPowerSeries j)) =
        MvPowerSeries.subst (Sum.elim yv zv) (X.F.toPowerSeries j)
      rw [MvPowerSeries.subst_comp_subst_apply hyz hψ]
      congr 1
      funext l
      rcases l with l | l <;> simp only [yv, zv, Sum.elim_inl, Sum.elim_inr, subst_X hψ]
    · simp only [sv, Sum.elim_inr, subst_X hψ]
  have e2 : (fun s => MvPowerSeries.subst
      (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) B)) ux)
      (Sum.elim yv sv s)) = Sum.elim yv ux := by
    funext s
    rcases s with l | t <;> simp only [yv, sv, Sum.elim_inl, Sum.elim_inr, subst_X hψ]
  rw [e1, e2, subst_elim_rename_swap Fyz ux hFyz hux, subst_elim_rename_swap yv ux hy hux]

  rw [show (Sum.elim ux Fyz) = Sum.elim (fun j => MvPowerSeries.subst sv (u j)) Fyz from rfl,
    show (Sum.elim ux yv) = Sum.elim (fun j => MvPowerSeries.subst sv (u j)) yv from rfl,
    subst_elim_substu u hu0 2 sv Fyz hs hFyz, subst_elim_substu u hu0 2 sv yv hs hy,
    subst_uT_W₁ X I hfin hproj u hu0 huinv hdesc i]
  unfold w
  rw [subst_elim_subst_law X.F sv Fyz hs hFyz, subst_elim_subst_law X.F sv yv hs hy]

  have key : (fun j => MvPowerSeries.subst (Sum.elim sv Fyz) (X.F.toPowerSeries j)) =
      fun j => MvPowerSeries.subst (Sum.elim Fxy zv) (X.F.toPowerSeries j) :=
    funext fun j => (law_assoc_subst X.F sv yv zv hs hy hz j).symm
  rw [key]
  exact inv_transport X.F I (u i) (huinv i) Fxy hFxy (fun l => Sum.inl (Sum.inr l))

noncomputable def G' (i : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  (hdesc 2 _ (invN_W₁_swap X I hfin hproj u hu0 huinv hdesc i)).choose

theorem subst_uT_G' (i : Fin 2) :
    MvPowerSeries.subst (uT u 2) (G' X I hfin hproj u hu0 huinv hdesc i) =
      MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (W₁ X I hfin hproj u hu0 huinv hdesc i) :=
  (hdesc 2 _ (invN_W₁_swap X I hfin hproj u hu0 huinv hdesc i)).choose_spec.1

noncomputable def G₀ (i : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (G' X I hfin hproj u hu0 huinv hdesc i)

theorem subst_uLR_G₀ (i : Fin 2) :
    MvPowerSeries.subst (uLR u) (G₀ X I hfin hproj u hu0 huinv hdesc i) = MvPowerSeries.subst X.F.toPowerSeries (u i) := by
  rw [subst_uLR_eq' u hu0]
  show MvPowerSeries.subst (uT u 2) (MvPowerSeries.subst (xuR u)
    (MvPowerSeries.rename (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) (G' X I hfin hproj u hu0 huinv hdesc i))) = _
  rw [subst_xuR_eq u hu0, rename_swap_swap, subst_uT_G' X I hfin hproj u hu0 huinv hdesc i, rename_swap_swap,
    subst_uT_W₁ X I hfin hproj u hu0 huinv hdesc i]
  rfl

theorem subst_G₀_pair {τ : Type} (a b : Fin 2 → MvPowerSeries τ B)
    (ha : ∀ l, constantCoeff (a l) = 0) (hb : ∀ l, constantCoeff (b l) = 0) (i : Fin 2) :
    MvPowerSeries.subst (Sum.elim (fun j => MvPowerSeries.subst a (u j)) (fun j => MvPowerSeries.subst b (u j)))
        (G₀ X I hfin hproj u hu0 huinv hdesc i) =
      MvPowerSeries.subst (fun l => MvPowerSeries.subst (Sum.elim a b) (X.F.toPowerSeries l)) (u i) := by
  have hab : HasSubst (Sum.elim a b) := hasSubst_of_constantCoeff_zero (by rintro (l | l); exacts [ha l, hb l])
  have hD := congrArg (MvPowerSeries.subst (Sum.elim a b)) (subst_uLR_G₀ X I hfin hproj u hu0 huinv hdesc i)
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_uLR u hu0) hab,
    MvPowerSeries.subst_comp_subst_apply X.F.hasSubst_toPowerSeries hab] at hD
  have htup : (Sum.elim (fun j => MvPowerSeries.subst a (u j)) (fun j => MvPowerSeries.subst b (u j))) =
      fun s => MvPowerSeries.subst (Sum.elim a b) (uLR u s) := by
    funext s
    rcases s with j | j
    · show MvPowerSeries.subst a (u j) = MvPowerSeries.subst (Sum.elim a b)
        (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
      rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) hab]
      congr 1
      funext l
      rw [subst_X hab]
      rfl
    · show MvPowerSeries.subst b (u j) = MvPowerSeries.subst (Sum.elim a b)
        (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j))
      rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) hab]
      congr 1
      funext l
      rw [subst_X hab]
      rfl
  rw [htup]
  exact hD

theorem constantCoeff_G₀ (i : Fin 2) : MvPowerSeries.constantCoeff (G₀ X I hfin hproj u hu0 huinv hdesc i) = 0 := by
  rw [← constantCoeff_subst_of_constantCoeff_zero (uLR u) (constantCoeff_uLR u hu0) (G₀ X I hfin hproj u hu0 huinv hdesc i),
    subst_uLR_G₀ X I hfin hproj u hu0 huinv hdesc i]
  exact MvPowerSeries.constantCoeff_subst_eq_zero X.F.hasSubst_toPowerSeries X.F.constantCoeff_eq_zero (hu0 i)

theorem coeff_single_inl_G₀ (i j : Fin 2) :
    (G₀ X I hfin hproj u hu0 huinv hdesc i).coeff (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0 := by
  classical
  have hu := hasSubst_of_constantCoeff_zero hu0
  have hZ0 : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff (Sum.elim (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B))
      (fun _ => (0 : MvPowerSeries (Fin 2) B)) s) = 0 := by
    rintro (l | l)
    · exact MvPowerSeries.constantCoeff_X _
    · exact map_zero _
  have hZ := hasSubst_of_constantCoeff_zero hZ0

  have hK : MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B))
      (fun _ => (0 : MvPowerSeries (Fin 2) B))) (G₀ X I hfin hproj u hu0 huinv hdesc i) = MvPowerSeries.X i := by
    apply subst_u_injective X I u hu0 hdesc
    rw [subst_X hu, MvPowerSeries.subst_comp_subst_apply hZ hu]
    have htup : (fun s => MvPowerSeries.subst u (Sum.elim (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B))
        (fun _ => (0 : MvPowerSeries (Fin 2) B)) s)) =
        Sum.elim (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B)) (u j))
          (fun j => MvPowerSeries.subst (fun _ => (0 : MvPowerSeries (Fin 2) B)) (u j)) := by
      funext s
      rcases s with l | l
      · show MvPowerSeries.subst u (MvPowerSeries.X l) = MvPowerSeries.subst MvPowerSeries.X (u l)
        rw [subst_X hu, MvPowerSeries.subst_self]
        rfl
      · show MvPowerSeries.subst u 0 = MvPowerSeries.subst (fun _ => (0 : MvPowerSeries (Fin 2) B)) (u l)
        rw [MvFormalGroup.subst_zero_of_constantCoeff_eq_zero (hu0 l), ← MvPowerSeries.coe_substAlgHom hu, map_zero]
    rw [htup, subst_G₀_pair X I hfin hproj u hu0 huinv hdesc _ _ (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => map_zero _) i]
    have hF : (fun l => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B))
        (fun _ => (0 : MvPowerSeries (Fin 2) B))) (X.F.toPowerSeries l)) = fun l => MvPowerSeries.X l := by
      funext l
      exact MvFormalGroup.subst_elim_X_zero X.F l
    rw [hF]
    exact congrFun MvPowerSeries.subst_self (u i)
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) hK
  rw [MvFormalGroup.coeff_single_subst hZ0 _ j, Fintype.sum_sum_type, MvPowerSeries.coeff_index_single_X] at hc
  simp only [Sum.elim_inl, Sum.elim_inr, map_zero, mul_zero, Finset.sum_const_zero, add_zero,
    MvPowerSeries.coeff_index_single_X, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hc
  rw [hc]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem coeff_single_inr_G₀ (i j : Fin 2) :
    (G₀ X I hfin hproj u hu0 huinv hdesc i).coeff (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0 := by
  classical
  have hu := hasSubst_of_constantCoeff_zero hu0
  have hZ0 : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff (Sum.elim (fun _ => (0 : MvPowerSeries (Fin 2) B))
      (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B)) s) = 0 := by
    rintro (l | l)
    · exact map_zero _
    · exact MvPowerSeries.constantCoeff_X _
  have hZ := hasSubst_of_constantCoeff_zero hZ0

  have hK : MvPowerSeries.subst (Sum.elim (fun _ => (0 : MvPowerSeries (Fin 2) B))
      (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B))) (G₀ X I hfin hproj u hu0 huinv hdesc i) = MvPowerSeries.X i := by
    apply subst_u_injective X I u hu0 hdesc
    rw [subst_X hu, MvPowerSeries.subst_comp_subst_apply hZ hu]
    have htup : (fun s => MvPowerSeries.subst u (Sum.elim (fun _ => (0 : MvPowerSeries (Fin 2) B))
        (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B)) s)) =
        Sum.elim (fun j => MvPowerSeries.subst (fun _ => (0 : MvPowerSeries (Fin 2) B)) (u j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B)) (u j)) := by
      funext s
      rcases s with l | l
      · show MvPowerSeries.subst u 0 = MvPowerSeries.subst (fun _ => (0 : MvPowerSeries (Fin 2) B)) (u l)
        rw [MvFormalGroup.subst_zero_of_constantCoeff_eq_zero (hu0 l), ← MvPowerSeries.coe_substAlgHom hu, map_zero]
      · show MvPowerSeries.subst u (MvPowerSeries.X l) = MvPowerSeries.subst MvPowerSeries.X (u l)
        rw [subst_X hu, MvPowerSeries.subst_self]
        rfl
    rw [htup, subst_G₀_pair X I hfin hproj u hu0 huinv hdesc _ _ (fun _ => map_zero _) (fun _ => MvPowerSeries.constantCoeff_X _) i]
    have hF : (fun l => MvPowerSeries.subst (Sum.elim (fun _ => (0 : MvPowerSeries (Fin 2) B))
        (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) B))) (X.F.toPowerSeries l)) = fun l => MvPowerSeries.X l := by
      funext l
      exact MvFormalGroup.subst_elim_zero_X X.F l
    rw [hF]
    exact congrFun MvPowerSeries.subst_self (u i)
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) hK
  rw [MvFormalGroup.coeff_single_subst hZ0 _ j, Fintype.sum_sum_type, MvPowerSeries.coeff_index_single_X] at hc
  simp only [Sum.elim_inl, Sum.elim_inr, map_zero, mul_zero, Finset.sum_const_zero, zero_add,
    MvPowerSeries.coeff_index_single_X, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hc
  rw [hc]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem assoc_G₀ (i : Fin 2) :
    MvPowerSeries.subst
      (Sum.elim
        (fun j => MvPowerSeries.subst
          (Sum.elim
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))
            fun l => MvPowerSeries.X (Sum.inr (Sum.inl l)))
          (G₀ X I hfin hproj u hu0 huinv hdesc j))
        fun j => MvPowerSeries.X (Sum.inr (Sum.inr j)))
      (G₀ X I hfin hproj u hu0 huinv hdesc i)
      =
    MvPowerSeries.subst
      (Sum.elim
        (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))
        fun j => MvPowerSeries.subst
          (Sum.elim
            (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))
            fun l => MvPowerSeries.X (Sum.inr (Sum.inr l)))
          (G₀ X I hfin hproj u hu0 huinv hdesc j))
      (G₀ X I hfin hproj u hu0 huinv hdesc i) := by
  have hvx : ∀ l, MvPowerSeries.constantCoeff ((fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hvy : ∀ l, MvPowerSeries.constantCoeff ((fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hvz : ∀ l, MvPowerSeries.constantCoeff ((fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) l) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
  have hT : HasSubst (T u) := hasSubst_of_constantCoeff_zero (cc_T u hu0)
  have hG0 : ∀ j, MvPowerSeries.constantCoeff (G₀ X I hfin hproj u hu0 huinv hdesc j) = 0 :=
    constantCoeff_G₀ X I hfin hproj u hu0 huinv hdesc
  have hxy : HasSubst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) := hasSubst_of_constantCoeff_zero (cc_elim hvx hvy)
  have hyz : HasSubst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) := hasSubst_of_constantCoeff_zero (cc_elim hvy hvz)
  have hFxy : ∀ j, MvPowerSeries.constantCoeff (MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (X.F.toPowerSeries j)) = 0 :=
    cc_substF X.F (cc_elim hvx hvy)
  have hFyz : ∀ j, MvPowerSeries.constantCoeff (MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (X.F.toPowerSeries j)) = 0 :=
    cc_substF X.F (cc_elim hvy hvz)
  have hGxy : HasSubst (Sum.elim
      (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (G₀ X I hfin hproj u hu0 huinv hdesc j)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) :=
    hasSubst_of_constantCoeff_zero (cc_elim
      (fun j => MvPowerSeries.constantCoeff_subst_eq_zero hxy (cc_elim hvx hvy) (hG0 j)) hvz)
  have hGyz : HasSubst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))
      (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (G₀ X I hfin hproj u hu0 huinv hdesc j))) :=
    hasSubst_of_constantCoeff_zero (cc_elim hvx
      (fun j => MvPowerSeries.constantCoeff_subst_eq_zero hyz (cc_elim hvy hvz) (hG0 j)))
  apply subst_T_injective X I u hu0 hdesc
  show MvPowerSeries.subst (T u) (MvPowerSeries.subst
      (Sum.elim (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (G₀ X I hfin hproj u hu0 huinv hdesc j)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)))
      (G₀ X I hfin hproj u hu0 huinv hdesc i)) =
    MvPowerSeries.subst (T u) (MvPowerSeries.subst
      (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (G₀ X I hfin hproj u hu0 huinv hdesc j)))
      (G₀ X I hfin hproj u hu0 huinv hdesc i))
  rw [MvPowerSeries.subst_comp_subst_apply hGxy hT, MvPowerSeries.subst_comp_subst_apply hGyz hT]

  have tX : ∀ l, MvPowerSeries.subst (T u) (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B) = MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u l) := fun l => by
    rw [subst_X hT, T_def, Sum.elim_inl]
  have tY : ∀ l, MvPowerSeries.subst (T u) (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B) = MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u l) := fun l => by
    rw [subst_X hT, T_def, Sum.elim_inr, Sum.elim_inl]
  have tZ : ∀ l, MvPowerSeries.subst (T u) (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B) = MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u l) := fun l => by
    rw [subst_X hT, T_def, Sum.elim_inr, Sum.elim_inr]

  have eL : (fun s => MvPowerSeries.subst (T u)
      (Sum.elim (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (G₀ X I hfin hproj u hu0 huinv hdesc j)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) s)) =
      Sum.elim (fun k => MvPowerSeries.subst (fun k => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (X.F.toPowerSeries k)) (u k))
        (fun k => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u k)) := by
    funext s
    rcases s with j | l
    · simp only [Sum.elim_inl]
      rw [MvPowerSeries.subst_comp_subst_apply hxy hT]
      have e' : (fun v => MvPowerSeries.subst (T u) (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) v)) =
          Sum.elim (fun k => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u k)) (fun k => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u k)) := by
        funext v
        rcases v with l | l
        · simp only [Sum.elim_inl, tX]
        · simp only [Sum.elim_inr, Sum.elim_inl, tY]
      rw [e', subst_G₀_pair X I hfin hproj u hu0 huinv hdesc (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) hvx hvy]
    · simp only [Sum.elim_inr, tZ]

  have eR : (fun s => MvPowerSeries.subst (T u)
      (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun j => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (G₀ X I hfin hproj u hu0 huinv hdesc j)) s)) =
      Sum.elim (fun k => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u k))
        (fun k => MvPowerSeries.subst (fun k => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (X.F.toPowerSeries k)) (u k)) := by
    funext s
    rcases s with l | j
    · simp only [Sum.elim_inl, tX]
    · simp only [Sum.elim_inr]
      rw [MvPowerSeries.subst_comp_subst_apply hyz hT]
      have e' : (fun v => MvPowerSeries.subst (T u) (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) v)) =
          Sum.elim (fun k => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u k)) (fun k => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (u k)) := by
        funext v
        rcases v with l | l
        · simp only [Sum.elim_inl, tY]
        · simp only [Sum.elim_inr, tZ]
      rw [e', subst_G₀_pair X I hfin hproj u hu0 huinv hdesc (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) hvy hvz]
  rw [eL, eR, subst_G₀_pair X I hfin hproj u hu0 huinv hdesc _ (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) hFxy hvz,
    subst_G₀_pair X I hfin hproj u hu0 huinv hdesc (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) _ hvx hFyz]

  have key : (fun k => MvPowerSeries.subst (Sum.elim
        (fun k => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (X.F.toPowerSeries k)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (X.F.toPowerSeries k)) =
      fun k => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))
        (fun k => MvPowerSeries.subst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B))) (X.F.toPowerSeries k))) (X.F.toPowerSeries k) :=
    funext fun k => law_assoc_subst X.F (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) (fun l => (MvPowerSeries.X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) B)) hvx hvy hvz k
  rw [key]

noncomputable def Glaw : MvFormalGroup 2 B where
  toPowerSeries := G₀ X I hfin hproj u hu0 huinv hdesc
  constantCoeff_eq_zero := constantCoeff_G₀ X I hfin hproj u hu0 huinv hdesc
  coeff_single_inl := coeff_single_inl_G₀ X I hfin hproj u hu0 huinv hdesc
  coeff_single_inr := coeff_single_inr_G₀ X I hfin hproj u hu0 huinv hdesc
  assoc := assoc_G₀ X I hfin hproj u hu0 huinv hdesc

theorem isComm_Glaw : (Glaw X I hfin hproj u hu0 huinv hdesc).IsComm := by
  constructor
  intro i
  show MvPowerSeries.subst (Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
      (fun j => MvPowerSeries.X (Sum.inl j))) (G₀ X I hfin hproj u hu0 huinv hdesc i) = G₀ X I hfin hproj u hu0 huinv hdesc i
  have hsw : (Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
      (fun j => MvPowerSeries.X (Sum.inl j))) =
      (MvPowerSeries.X ∘ (Sum.swap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2)) := by
    funext v
    rcases v with j | j <;> rfl
  rw [hsw, ← MvPowerSeries.rename_eq_subst]
  apply subst_uLR_injective X I u hu0 hdesc
  rw [subst_uLR_rename_swap u hu0, subst_uLR_G₀ X I hfin hproj u hu0 huinv hdesc i,
    rename_subst _ _ X.F.constantCoeff_eq_zero]
  congr 1
  funext j
  have hc := X.isComm.comm j
  rw [hsw, ← MvPowerSeries.rename_eq_subst] at hc
  exact hc

theorem isLawHom_Glaw : IsLawHom X.F (Glaw X I hfin hproj u hu0 huinv hdesc) u :=
  ⟨hu0, fun i => (subst_uLR_G₀ X I hfin hproj u hu0 huinv hdesc i).symm⟩

theorem main : ∃ G : MvFormalGroup 2 B, G.IsComm ∧ IsLawHom X.F G u :=
  ⟨Glaw X I hfin hproj u hu0 huinv hdesc, isComm_Glaw X I hfin hproj u hu0 huinv hdesc, isLawHom_Glaw X I hfin hproj u hu0 huinv hdesc⟩

end LawDescent

end P2mD2

open P2mD2 in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
    (huinv : ∀ j, MvPowerSeries.subst X.F.toPowerSeries (u j) -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u j) ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B))))
    (hdesc : ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w) :
    ∃ G : MvFormalGroup 2 B, G.IsComm ∧ IsLawHom X.F G u :=
  P2mD2.main X I hfin hproj u hu0 huinv hdesc

end S_CerednikDrinfeld_FormalODModule_exists_mvFormalGroup_isComm_isLawHom_of_invariant_coordinates
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_mvFormalGroup_isComm_isLawHom_of_invariant_coordinates (solution)
