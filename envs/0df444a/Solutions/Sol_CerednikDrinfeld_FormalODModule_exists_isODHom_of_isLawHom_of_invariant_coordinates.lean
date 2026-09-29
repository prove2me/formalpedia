-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isODHom_of_isLawHom_of_invariant_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d0bd1076-7397-5845-8de5-89d312f61e9a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_of_isLawHom_of_invariant_coordinates

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff X subst_X)

namespace P2mD3

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

end P2mD3

namespace P2mD3

section Desc0

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

noncomputable abbrev ren : MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2 ⊕ Fin 0) B :=
  MvPowerSeries.rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 0)

noncomputable abbrev ren4 : MvPowerSeries (Fin 2 ⊕ Fin 2) B →ₐ[B] MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B :=
  MvPowerSeries.rename (Sum.inl : Fin 2 ⊕ Fin 2 → (Fin 2 ⊕ Fin 2) ⊕ Fin 0)

omit hu0 hdesc in
theorem ren_injective : Function.Injective (ren (B := B)) :=
  MvPowerSeries.rename_injective (R := B) ⟨Sum.inl, Sum.inl_injective⟩

omit hu0 hdesc in

theorem inl_comp_sumEmpty : (Sum.inl ∘ (Equiv.sumEmpty (Fin 2) (Fin 0))) = (id : Fin 2 ⊕ Fin 0 → Fin 2 ⊕ Fin 0) := by
  funext v
  rcases v with j | t
  · rfl
  · exact (IsEmpty.false t).elim

omit hu0 hdesc in
theorem rename_eq_self_of_eq_id {σ : Type} (f : σ → σ) [Filter.TendstoCofinite f] (hf : f = id) (q : MvPowerSeries σ B) :
    MvPowerSeries.rename f q = q := by
  subst hf
  exact MvPowerSeries.rename_id_apply q

omit hu0 hdesc in
theorem ren_renameEquiv (W : MvPowerSeries (Fin 2 ⊕ Fin 0) B) :
    ren (MvPowerSeries.renameEquiv B (Equiv.sumEmpty (Fin 2) (Fin 0)) W) = W := by
  show MvPowerSeries.rename Sum.inl (MvPowerSeries.rename (Equiv.sumEmpty (Fin 2) (Fin 0)) W) = W
  rw [MvPowerSeries.rename_rename]
  exact rename_eq_self_of_eq_id _ inl_comp_sumEmpty W

include hu0 in

theorem ren_subst_u (V : MvPowerSeries (Fin 2) B) :
    ren (MvPowerSeries.subst u V) = MvPowerSeries.subst (uT u 0) (ren V) := by
  rw [rename_subst _ u hu0]
  show _ = MvPowerSeries.subst (uT u 0) (MvPowerSeries.rename Sum.inl V)
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp Sum.inl) (hasSubst_uT u hu0 0)]
  congr 1
  funext j
  show MvPowerSeries.rename Sum.inl (u j) = MvPowerSeries.subst (uT u 0) (MvPowerSeries.X (Sum.inl j))
  rw [subst_X (hasSubst_uT u hu0 0), MvPowerSeries.rename_eq_subst]
  rfl

theorem inv0_of_inv2 (w : MvPowerSeries (Fin 2) B)
    (hw : MvPowerSeries.subst X.F.toPowerSeries w -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B)))) :
    MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst
            (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))
              (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
            (X.F.toPowerSeries j))
          (fun t => MvPowerSeries.X (Sum.inr t))) (ren w) -
      MvPowerSeries.subst
        (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))
          (fun t => MvPowerSeries.X (Sum.inr t))) (ren w) ∈
      Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))) ''
          (I : Set (MvPowerSeries (Fin 2) B))) := by

  have hA : HasSubst (Sum.elim
      (fun j => MvPowerSeries.subst
        (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))
          (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
        (X.F.toPowerSeries j))
      (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | t)
    · exact MvPowerSeries.constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _))
        (by rintro (l | l) <;> exact MvPowerSeries.constantCoeff_X _) (X.F.constantCoeff_eq_zero j)
    · exact MvPowerSeries.constantCoeff_X _
  have hBt : HasSubst (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))
      (fun t => MvPowerSeries.X (Sum.inr t))) :=
    hasSubst_of_constantCoeff_zero (by rintro (l | t) <;> exact MvPowerSeries.constantCoeff_X _)
  have hXinl4 : ∀ v : Fin 2 ⊕ Fin 2, (MvPowerSeries.X (Sum.inl v) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B) =
      Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))
        (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))) v := by
    rintro (l | l) <;> rfl
  have h1 : MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst
            (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))
              (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
            (X.F.toPowerSeries j))
          (fun t => MvPowerSeries.X (Sum.inr t))) (ren w) = ren4 (MvPowerSeries.subst X.F.toPowerSeries w) := by
    rw [rename_subst _ _ X.F.constantCoeff_eq_zero]
    show MvPowerSeries.subst _ (MvPowerSeries.rename Sum.inl w) = _
    rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp Sum.inl) hA]
    congr 1
    funext j
    rw [Function.comp_apply, subst_X hA, Sum.elim_inl, MvPowerSeries.rename_eq_subst]
    congr 1
    funext v
    exact (hXinl4 v).symm
  have h2 : MvPowerSeries.subst
        (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))
          (fun t => MvPowerSeries.X (Sum.inr t))) (ren w) =
      ren4 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w) := by
    rw [rename_subst _ _ (fun _ => MvPowerSeries.constantCoeff_X _)]
    show MvPowerSeries.subst _ (MvPowerSeries.rename Sum.inl w) = _
    rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp Sum.inl) hBt]
    congr 1
    funext l
    rw [Function.comp_apply, subst_X hBt, Sum.elim_inl, MvPowerSeries.rename_X]
  rw [h1, h2, ← map_sub]

  have hgen : ∀ f ∈ I, ren4 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) f) ∈
      Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))) ''
          (I : Set (MvPowerSeries (Fin 2) B))) := by
    intro f hf
    apply Ideal.subset_span
    refine ⟨f, hf, ?_⟩
    rw [rename_subst _ _ (fun _ => MvPowerSeries.constantCoeff_X _)]
    congr 1
    funext l
    rw [MvPowerSeries.rename_X]
  have hle : Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B))) ≤
      (Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) B))) ''
          (I : Set (MvPowerSeries (Fin 2) B)))).comap (ren4 (B := B) : _ →+* _) := by
    rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact hgen f hf
  exact hle hw

noncomputable def desc0 (w : MvPowerSeries (Fin 2) B)
    (hw : MvPowerSeries.subst X.F.toPowerSeries w -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B)))) : MvPowerSeries (Fin 2) B :=
  MvPowerSeries.renameEquiv B (Equiv.sumEmpty (Fin 2) (Fin 0)) (hdesc 0 (ren w) (inv0_of_inv2 X I w hw)).choose

include hu0 in
theorem subst_u_desc0 (w : MvPowerSeries (Fin 2) B) (hw) : MvPowerSeries.subst u (desc0 X I u hdesc w hw) = w := by
  apply ren_injective
  rw [ren_subst_u u hu0]
  unfold desc0
  rw [ren_renameEquiv]
  exact (hdesc 0 (ren w) (inv0_of_inv2 X I w hw)).choose_spec.1

include hu0 in

theorem eq_desc0 (w : MvPowerSeries (Fin 2) B) (hw) (V : MvPowerSeries (Fin 2) B) (hV : MvPowerSeries.subst u V = w) :
    V = desc0 X I u hdesc w hw := by
  apply ren_injective
  have h1 : MvPowerSeries.subst (uT u 0) (ren V) = ren w := by rw [← ren_subst_u u hu0, hV]
  have h2 : MvPowerSeries.subst (uT u 0) (ren (desc0 X I u hdesc w hw)) = ren w := by
    rw [← ren_subst_u u hu0, subst_u_desc0 X I u hu0 hdesc]
  exact subst_uT_injective X I u hu0 hdesc 0 (h1.trans h2.symm)

include hu0 hdesc in

theorem subst_u_injective : Function.Injective (MvPowerSeries.subst (R := B) u) := by
  intro V V' h
  apply ren_injective
  apply subst_uT_injective X I u hu0 hdesc 0
  rw [← ren_subst_u u hu0, ← ren_subst_u u hu0, h]

end Desc0

end P2mD3

namespace P2mD3

section InvS

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)

def Inv2 (w : MvPowerSeries (Fin 2) B) : Prop :=
  MvPowerSeries.subst X.F.toPowerSeries w -
      MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w ∈
    Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
      (I : Set (MvPowerSeries (Fin 2) B)))

variable (s : Series B) (hs0 : ∀ i, MvPowerSeries.constantCoeff (s i) = 0)
  (hslaw : ∀ i, MvPowerSeries.subst X.F.toPowerSeries (s i) =
    MvPowerSeries.subst
      (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (s j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (s j)))
      (X.F.toPowerSeries i))
  (hsI : ∀ f ∈ I, MvPowerSeries.subst s f ∈ I)

noncomputable def S4 : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  Sum.elim
    (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (s j))
    (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (s j))

include hs0 in
theorem hasSubst_S4 : HasSubst (S4 s) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (j | j)
  · exact MvPowerSeries.constantCoeff_subst_eq_zero
      (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hs0 j)
  · exact MvPowerSeries.constantCoeff_subst_eq_zero
      (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => MvPowerSeries.constantCoeff_X _) (hs0 j)

omit hu0 in
include hs0 hslaw hsI in

theorem inv2_subst (w : MvPowerSeries (Fin 2) B) (hw : Inv2 X I w) : Inv2 X I (MvPowerSeries.subst s w) := by
  have hXl : HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  have hXr : HasSubst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  have hs := hasSubst_of_constantCoeff_zero hs0
  unfold Inv2

  have h1 : MvPowerSeries.subst X.F.toPowerSeries (MvPowerSeries.subst s w) =
      MvPowerSeries.subst (S4 s) (MvPowerSeries.subst X.F.toPowerSeries w) := by
    rw [MvPowerSeries.subst_comp_subst_apply hs X.F.hasSubst_toPowerSeries,
      MvPowerSeries.subst_comp_subst_apply X.F.hasSubst_toPowerSeries (hasSubst_S4 s hs0)]
    congr 1
    funext i
    exact hslaw i

  have h2 : MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (MvPowerSeries.subst s w) =
      MvPowerSeries.subst (S4 s) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w) := by
    rw [MvPowerSeries.subst_comp_subst_apply hs hXl, MvPowerSeries.subst_comp_subst_apply hXl (hasSubst_S4 s hs0)]
    congr 1
    funext i
    rw [subst_X (hasSubst_S4 s hs0)]
    rfl
  rw [h1, h2, ← MvPowerSeries.coe_substAlgHom (hasSubst_S4 s hs0), ← map_sub]

  have hle : Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B))) ≤
      (Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B)))).comap
        ((MvPowerSeries.substAlgHom (R := B) (hasSubst_S4 s hs0) : _ →ₐ[B] _) : _ →+* _) := by
    rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    show MvPowerSeries.substAlgHom (R := B) (hasSubst_S4 s hs0)
        (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) f) ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B)))
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_comp_subst_apply hXr (hasSubst_S4 s hs0)]
    apply Ideal.subset_span
    refine ⟨MvPowerSeries.subst s f, hsI f hf, ?_⟩
    rw [MvPowerSeries.subst_comp_subst_apply hs hXr]
    congr 1
    funext i
    rw [subst_X (hasSubst_S4 s hs0)]
    rfl
  exact hle hw

end InvS

end P2mD3

namespace P2mD3

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

end P2mD3

namespace P2mD3

section Action

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (hact : ∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst (X.act a) f ∈ I)
  (hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I)
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

noncomputable def actY (a : Zp2 p) : Series B := fun j =>
  desc0 X I u hdesc (MvPowerSeries.subst (X.act a) (u j))
    (inv2_subst X I (X.act a) (X.isLawHom_act a).1 (X.isLawHom_act a).2 (hact a) (u j) (huinv j))

noncomputable def varpiY : Series B := fun j =>
  desc0 X I u hdesc (MvPowerSeries.subst X.varpi (u j))
    (inv2_subst X I X.varpi X.isLawHom_varpi.1 X.isLawHom_varpi.2 hvarpi (u j) (huinv j))

include hu0 in
theorem subst_u_actY (a : Zp2 p) (j : Fin 2) :
    MvPowerSeries.subst u (actY X I hact u huinv hdesc a j) = MvPowerSeries.subst (X.act a) (u j) :=
  subst_u_desc0 X I u hu0 hdesc _ _

include hu0 in
theorem subst_u_varpiY (j : Fin 2) :
    MvPowerSeries.subst u (varpiY X I hvarpi u huinv hdesc j) = MvPowerSeries.subst X.varpi (u j) :=
  subst_u_desc0 X I u hu0 hdesc _ _

include hu0 in

theorem eq_actY (a : Zp2 p) (T : Series B) (hT : ∀ j, MvPowerSeries.subst u (T j) = MvPowerSeries.subst (X.act a) (u j)) :
    T = actY X I hact u huinv hdesc a :=
  funext fun j => eq_desc0 X I u hu0 hdesc _ _ (T j) (hT j)

include hu0 in
theorem eq_varpiY (T : Series B) (hT : ∀ j, MvPowerSeries.subst u (T j) = MvPowerSeries.subst X.varpi (u j)) :
    T = varpiY X I hvarpi u huinv hdesc :=
  funext fun j => eq_desc0 X I u hu0 hdesc _ _ (T j) (hT j)

include hu0 in
theorem actY0 (a : Zp2 p) (j : Fin 2) : constantCoeff (actY X I hact u huinv hdesc a j) = 0 := by
  rw [← constantCoeff_subst_u u hu0, subst_u_actY X I hact u hu0 huinv hdesc]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (X.isLawHom_act a).hasSubst (X.isLawHom_act a).1 (hu0 j)

include hu0 in
theorem varpiY0 (j : Fin 2) : constantCoeff (varpiY X I hvarpi u huinv hdesc j) = 0 := by
  rw [← constantCoeff_subst_u u hu0, subst_u_varpiY X I hvarpi u hu0 huinv hdesc]
  exact MvPowerSeries.constantCoeff_subst_eq_zero X.isLawHom_varpi.hasSubst X.isLawHom_varpi.1 (hu0 j)

omit huinv hdesc in
include hu0 in

theorem subst_u_subst (T : Series B) (hT0 : ∀ j, constantCoeff (T j) = 0) (V : MvPowerSeries (Fin 2) B) :
    MvPowerSeries.subst u (MvPowerSeries.subst T V) =
      MvPowerSeries.subst (fun j => MvPowerSeries.subst u (T j)) V :=
  MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hT0) (hasSubst_of_constantCoeff_zero hu0) V

include hu0 in

theorem actY_one : actY X I hact u huinv hdesc 1 = Series.id B := by
  symm
  apply eq_actY X I hact u hu0 huinv hdesc
  intro j
  rw [X.act_one]
  show MvPowerSeries.subst u (MvPowerSeries.X j) = MvPowerSeries.subst (fun i => MvPowerSeries.X i) (u j)
  rw [subst_X (hasSubst_of_constantCoeff_zero hu0), MvPowerSeries.subst_self]
  rfl

include hu0 in

theorem actY_mul (a b : Zp2 p) :
    actY X I hact u huinv hdesc (a * b) = (actY X I hact u huinv hdesc a).comp (actY X I hact u huinv hdesc b) := by
  symm
  apply eq_actY X I hact u hu0 huinv hdesc
  intro j
  show MvPowerSeries.subst u (MvPowerSeries.subst (actY X I hact u huinv hdesc b) (actY X I hact u huinv hdesc a j)) = _
  rw [subst_u_subst u hu0 _ (actY0 X I hact u hu0 huinv hdesc b)]
  simp only [subst_u_actY X I hact u hu0 huinv hdesc]
  rw [← MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hu0) (X.isLawHom_act b).hasSubst,
    subst_u_actY X I hact u hu0 huinv hdesc, X.act_mul,
    MvPowerSeries.subst_comp_subst_apply (X.isLawHom_act a).hasSubst (X.isLawHom_act b).hasSubst]
  rfl

include hu0 in

theorem varpiY_comp_varpiY :
    (varpiY X I hvarpi u huinv hdesc).comp (varpiY X I hvarpi u huinv hdesc) = actY X I hact u huinv hdesc (p : Zp2 p) := by
  apply eq_actY X I hact u hu0 huinv hdesc
  intro j
  show MvPowerSeries.subst u (MvPowerSeries.subst (varpiY X I hvarpi u huinv hdesc) (varpiY X I hvarpi u huinv hdesc j)) = _
  rw [subst_u_subst u hu0 _ (varpiY0 X I hvarpi u hu0 huinv hdesc)]
  simp only [subst_u_varpiY X I hvarpi u hu0 huinv hdesc]
  rw [← MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hu0) X.isLawHom_varpi.hasSubst,
    subst_u_varpiY X I hvarpi u hu0 huinv hdesc, ← X.varpi_comp_varpi,
    MvPowerSeries.subst_comp_subst_apply X.isLawHom_varpi.hasSubst X.isLawHom_varpi.hasSubst]
  rfl

include hu0 in

theorem varpiY_comp_actY (a : Zp2 p) :
    (varpiY X I hvarpi u huinv hdesc).comp (actY X I hact u huinv hdesc a) =
      (actY X I hact u huinv hdesc (WittVector.frobenius a)).comp (varpiY X I hvarpi u huinv hdesc) := by

  have h1 : ∀ j, MvPowerSeries.subst u (((varpiY X I hvarpi u huinv hdesc).comp (actY X I hact u huinv hdesc a)) j) =
      MvPowerSeries.subst ((X.varpi).comp (X.act a)) (u j) := by
    intro j
    show MvPowerSeries.subst u (MvPowerSeries.subst (actY X I hact u huinv hdesc a) (varpiY X I hvarpi u huinv hdesc j)) = _
    rw [subst_u_subst u hu0 _ (actY0 X I hact u hu0 huinv hdesc a)]
    simp only [subst_u_actY X I hact u hu0 huinv hdesc]
    rw [← MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hu0) (X.isLawHom_act a).hasSubst,
      subst_u_varpiY X I hvarpi u hu0 huinv hdesc,
      MvPowerSeries.subst_comp_subst_apply X.isLawHom_varpi.hasSubst (X.isLawHom_act a).hasSubst]
    rfl
  have h2 : ∀ j, MvPowerSeries.subst u (((actY X I hact u huinv hdesc (WittVector.frobenius a)).comp (varpiY X I hvarpi u huinv hdesc)) j) =
      MvPowerSeries.subst ((X.act (WittVector.frobenius a)).comp X.varpi) (u j) := by
    intro j
    show MvPowerSeries.subst u (MvPowerSeries.subst (varpiY X I hvarpi u huinv hdesc) (actY X I hact u huinv hdesc _ j)) = _
    rw [subst_u_subst u hu0 _ (varpiY0 X I hvarpi u hu0 huinv hdesc)]
    simp only [subst_u_varpiY X I hvarpi u hu0 huinv hdesc]
    rw [← MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hu0) X.isLawHom_varpi.hasSubst,
      subst_u_actY X I hact u hu0 huinv hdesc,
      MvPowerSeries.subst_comp_subst_apply (X.isLawHom_act _).hasSubst X.isLawHom_varpi.hasSubst]
    rfl
  funext j
  apply subst_u_injective X I u hu0 hdesc
  rw [h1, h2, X.varpi_comp_act]

end Action

end P2mD3

namespace P2mD3

section Assembly

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
  (hact : ∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst (X.act a) f ∈ I)
  (hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I)
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
  (G : MvFormalGroup 2 B) (hGc : G.IsComm) (hG : IsLawHom X.F G u)

omit hact hvarpi huinv hdesc hGc in
include hu0 hG in

theorem subst_F_u (j : Fin 2) :
    MvPowerSeries.subst X.F.toPowerSeries (u j) = MvPowerSeries.subst (uLR u) (G.toPowerSeries j) :=
  hG.2 j

include hu0 hG in

theorem actY_add (a b : Zp2 p) :
    actY X I hact u huinv hdesc (a + b) =
      Series.addVia G (actY X I hact u huinv hdesc a) (actY X I hact u huinv hdesc b) := by
  symm
  apply eq_actY X I hact u hu0 huinv hdesc
  intro j
  have hAB : HasSubst (Sum.elim (actY X I hact u huinv hdesc a) (actY X I hact u huinv hdesc b)) :=
    hasSubst_of_constantCoeff_zero (by
      rintro (i | i)
      · exact actY0 X I hact u hu0 huinv hdesc a i
      · exact actY0 X I hact u hu0 huinv hdesc b i)
  have hab : HasSubst (Sum.elim (X.act a) (X.act b)) :=
    hasSubst_of_constantCoeff_zero (by rintro (i | i); exacts [(X.isLawHom_act a).1 i, (X.isLawHom_act b).1 i])
  show MvPowerSeries.subst u (MvPowerSeries.subst (Sum.elim (actY X I hact u huinv hdesc a) (actY X I hact u huinv hdesc b))
    (G.toPowerSeries j)) = _
  rw [MvPowerSeries.subst_comp_subst_apply hAB (hasSubst_of_constantCoeff_zero hu0), X.act_add]
  show _ = MvPowerSeries.subst (fun i => MvPowerSeries.subst (Sum.elim (X.act a) (X.act b)) (X.F.toPowerSeries i)) (u j)
  rw [← MvPowerSeries.subst_comp_subst_apply X.F.hasSubst_toPowerSeries hab, subst_F_u X u hu0 G hG j,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_uLR u hu0) hab]
  congr 1
  funext v
  rcases v with i | i
  · show MvPowerSeries.subst u (actY X I hact u huinv hdesc a i) =
      MvPowerSeries.subst (Sum.elim (X.act a) (X.act b))
        (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u i))
    rw [subst_u_actY X I hact u hu0 huinv hdesc,
      MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) hab]
    congr 1
    funext l
    rw [subst_X hab]
    rfl
  · show MvPowerSeries.subst u (actY X I hact u huinv hdesc b i) =
      MvPowerSeries.subst (Sum.elim (X.act a) (X.act b))
        (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u i))
    rw [subst_u_actY X I hact u hu0 huinv hdesc,
      MvPowerSeries.subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) hab]
    congr 1
    funext l
    rw [subst_X hab]
    rfl

omit hact hvarpi huinv hGc in
include hu0 hdesc hG in

theorem law_desc (s : Series B) (hs0 : ∀ i, MvPowerSeries.constantCoeff (s i) = 0)
    (hslaw : ∀ i, MvPowerSeries.subst X.F.toPowerSeries (s i) =
      MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (s j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (s j)))
        (X.F.toPowerSeries i))
    (T : Series B) (hT0 : ∀ j, MvPowerSeries.constantCoeff (T j) = 0)
    (hT : ∀ j, MvPowerSeries.subst u (T j) = MvPowerSeries.subst s (u j)) (j : Fin 2) :
    MvPowerSeries.subst G.toPowerSeries (T j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (T i))
          (fun i => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (T i)))
        (G.toPowerSeries j) := by
  have hXl : HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  have hXr : HasSubst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  have hu := hasSubst_of_constantCoeff_zero hu0
  have hTs := hasSubst_of_constantCoeff_zero hT0
  have hs := hasSubst_of_constantCoeff_zero hs0
  have hTT : HasSubst (S4 T) := hasSubst_S4 T hT0
  apply subst_uLR_injective X I u hu0 hdesc

  rw [MvPowerSeries.subst_comp_subst_apply G.hasSubst_toPowerSeries (hasSubst_uLR u hu0)]
  have hGi : (fun i => MvPowerSeries.subst (uLR u) (G.toPowerSeries i)) = fun i => MvPowerSeries.subst X.F.toPowerSeries (u i) := by
    funext i; exact (subst_F_u X u hu0 G hG i).symm
  rw [hGi, ← MvPowerSeries.subst_comp_subst_apply hu X.F.hasSubst_toPowerSeries, hT j,
    MvPowerSeries.subst_comp_subst_apply hs X.F.hasSubst_toPowerSeries]
  have hsi : (fun i => MvPowerSeries.subst X.F.toPowerSeries (s i)) = fun i => MvPowerSeries.subst (S4 s) (X.F.toPowerSeries i) := by
    funext i; exact hslaw i
  rw [hsi, ← MvPowerSeries.subst_comp_subst_apply X.F.hasSubst_toPowerSeries (hasSubst_S4 s hs0), subst_F_u X u hu0 G hG j,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_uLR u hu0) (hasSubst_S4 s hs0)]

  show _ = MvPowerSeries.subst (uLR u) (MvPowerSeries.subst (S4 T) (G.toPowerSeries j))
  rw [MvPowerSeries.subst_comp_subst_apply hTT (hasSubst_uLR u hu0)]
  congr 1
  funext v
  rcases v with i | i
  · show MvPowerSeries.subst (S4 s) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u i)) =
      MvPowerSeries.subst (uLR u) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (T i))
    rw [MvPowerSeries.subst_comp_subst_apply hXl (hasSubst_S4 s hs0), MvPowerSeries.subst_comp_subst_apply hXl (hasSubst_uLR u hu0)]
    have e1 : (fun l => MvPowerSeries.subst (S4 s) (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) =
        fun l => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (s l) := by
      funext l; rw [subst_X (hasSubst_S4 s hs0)]; rfl
    have e2 : (fun l => MvPowerSeries.subst (uLR u) (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) =
        fun l => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u l) := by
      funext l; rw [subst_X (hasSubst_uLR u hu0)]; rfl
    rw [e1, e2, ← MvPowerSeries.subst_comp_subst_apply hs hXl, ← MvPowerSeries.subst_comp_subst_apply hu hXl, hT i]
  · show MvPowerSeries.subst (S4 s) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u i)) =
      MvPowerSeries.subst (uLR u) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (T i))
    rw [MvPowerSeries.subst_comp_subst_apply hXr (hasSubst_S4 s hs0), MvPowerSeries.subst_comp_subst_apply hXr (hasSubst_uLR u hu0)]
    have e1 : (fun l => MvPowerSeries.subst (S4 s) (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) =
        fun l => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (s l) := by
      funext l; rw [subst_X (hasSubst_S4 s hs0)]; rfl
    have e2 : (fun l => MvPowerSeries.subst (uLR u) (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) =
        fun l => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (u l) := by
      funext l; rw [subst_X (hasSubst_uLR u hu0)]; rfl
    rw [e1, e2, ← MvPowerSeries.subst_comp_subst_apply hs hXr, ← MvPowerSeries.subst_comp_subst_apply hu hXr, hT i]

noncomputable def Y : FormalODModule p B where
  F := G
  isComm := hGc
  act := actY X I hact u huinv hdesc
  varpi := varpiY X I hvarpi u huinv hdesc
  isLawHom_act a := ⟨actY0 X I hact u hu0 huinv hdesc a,
    law_desc X I u hu0 hdesc G hG (X.act a) (X.isLawHom_act a).1 (X.isLawHom_act a).2 _ (actY0 X I hact u hu0 huinv hdesc a)
      (subst_u_actY X I hact u hu0 huinv hdesc a)⟩
  isLawHom_varpi := ⟨varpiY0 X I hvarpi u hu0 huinv hdesc,
    law_desc X I u hu0 hdesc G hG X.varpi X.isLawHom_varpi.1 X.isLawHom_varpi.2 _ (varpiY0 X I hvarpi u hu0 huinv hdesc)
      (subst_u_varpiY X I hvarpi u hu0 huinv hdesc)⟩
  act_one := actY_one X I hact u hu0 huinv hdesc
  act_mul := actY_mul X I hact u hu0 huinv hdesc
  act_add := actY_add X I hact u hu0 huinv hdesc G hG
  varpi_comp_varpi := varpiY_comp_varpiY X I hact hvarpi u hu0 huinv hdesc
  varpi_comp_act := varpiY_comp_actY X I hact hvarpi u hu0 huinv hdesc

include hact hvarpi hu0 huinv hdesc hGc hG in
theorem main : ∃ Y : FormalODModule p B, Y.F = G ∧ FormalODModule.IsODHom X Y u :=
  ⟨Y X I hact hvarpi u hu0 huinv hdesc G hGc hG, rfl, hG,
    fun a => funext fun j => (subst_u_actY X I hact u hu0 huinv hdesc a j).symm,
    funext fun j => (subst_u_varpiY X I hvarpi u hu0 huinv hdesc j).symm⟩

end Assembly

end P2mD3

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hact : ∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst (X.act a) f ∈ I)
    (hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I)
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
    (G : MvFormalGroup 2 B) (hGc : G.IsComm) (hG : IsLawHom X.F G u) :
    ∃ Y : FormalODModule p B, Y.F = G ∧ FormalODModule.IsODHom X Y u :=
  P2mD3.main X I hact hvarpi u hu0 huinv hdesc G hGc hG

end S_CerednikDrinfeld_FormalODModule_exists_isODHom_of_isLawHom_of_invariant_coordinates
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_of_isLawHom_of_invariant_coordinates (solution)
