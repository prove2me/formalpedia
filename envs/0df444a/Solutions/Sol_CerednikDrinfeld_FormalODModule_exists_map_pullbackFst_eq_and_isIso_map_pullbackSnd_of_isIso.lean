-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8dfd6074-8b5f-5f55-b15d-e2412730145c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries (constantCoeff subst HasSubst hasSubst_of_constantCoeff_zero subst_X subst_comp_subst_apply constantCoeff_X constantCoeff_subst_eq_zero map_subst)

namespace OdGlue

section Generic
variable {g : ℕ} {R : Type*} [CommRing R] {τ : Type*}

theorem hom_subst_elim (F G : MvFormalGroup g R) (h : F.Hom G)
    (a b : Fin g → MvPowerSeries τ R) (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (i : Fin g) :
    subst (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) (h.toPowerSeries i) =
      subst (Sum.elim (fun j => subst a (h.toPowerSeries j)) (fun j => subst b (h.toPowerSeries j)))
        (G.toPowerSeries i) := by
  have hab : HasSubst (Sum.elim a b) := MvFormalGroup.hasSubst_elim ha hb
  have hXl : ∀ l : Fin g, constantCoeff ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) = 0 :=
    fun l => constantCoeff_X _
  have hXr : ∀ l : Fin g, constantCoeff ((MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) = 0 :=
    fun l => constantCoeff_X _
  have hA : HasSubst (Sum.elim
      (fun j => subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (h.toPowerSeries j))
      fun j => subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (h.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXl) hXl (h.constantCoeff_eq_zero j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXr) hXr (h.constantCoeff_eq_zero j)
  have key := congrArg (subst (Sum.elim a b)) (h.subst_eq i)
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries hab, subst_comp_subst_apply hA hab] at key
  have hfam : (fun s => subst (Sum.elim a b) (Sum.elim
      (fun j => subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (h.toPowerSeries j))
      (fun j => subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (h.toPowerSeries j)) s))
      = Sum.elim (fun j => subst a (h.toPowerSeries j)) (fun j => subst b (h.toPowerSeries j)) := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a b) (subst _ (h.toPowerSeries j)) = subst a (h.toPowerSeries j)
      rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hXl) hab]
      congr 1
      funext l
      exact subst_X hab _
    · show subst (Sum.elim a b) (subst _ (h.toPowerSeries j)) = subst b (h.toPowerSeries j)
      rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hXr) hab]
      congr 1
      funext l
      exact subst_X hab _
  rw [hfam] at key
  exact key

theorem isComm_of_hom_of_comp_eq_id (F G : MvFormalGroup g R) [F.IsComm] (Φ : G.Hom F) (Ψ : F.Hom G)
    (hΨΦ : Ψ.comp Φ = MvFormalGroup.Hom.id G) : G.IsComm := by
  refine ⟨fun i => ?_⟩

  have key : ∀ (A B : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R),
      (∀ j, (A j).constantCoeff = 0) → (∀ j, (B j).constantCoeff = 0) →
      subst (Sum.elim A B) (G.toPowerSeries i) =
        subst (fun j => subst (Sum.elim (fun l => subst A (Φ.toPowerSeries l)) (fun l => subst B (Φ.toPowerSeries l)))
          (F.toPowerSeries j)) (Ψ.toPowerSeries i) := by
    intro A B hA hB
    have hΦA : ∀ l, (subst A (Φ.toPowerSeries l)).constantCoeff = 0 := fun l =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hA) hA (Φ.constantCoeff_eq_zero l)
    have hΦB : ∀ l, (subst B (Φ.toPowerSeries l)).constantCoeff = 0 := fun l =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hB) hB (Φ.constantCoeff_eq_zero l)
    rw [hom_subst_elim F G Ψ _ _ hΦA hΦB i]

    have hid : ∀ (C : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R), (∀ j, (C j).constantCoeff = 0) →
        (fun j => subst (fun l => subst C (Φ.toPowerSeries l)) (Ψ.toPowerSeries j)) = C := by
      intro C hC
      funext j
      have h1 := congrArg (fun f : G.Hom G => f.toPowerSeries j) hΨΦ
      simp only [MvFormalGroup.Hom.comp, MvFormalGroup.Hom.id] at h1

      have h2 := congrArg (subst C) h1
      rw [subst_comp_subst_apply Φ.hasSubst_toPowerSeries (hasSubst_of_constantCoeff_zero hC),
        subst_X (hasSubst_of_constantCoeff_zero hC)] at h2
      exact h2
    rw [hid A hA, hid B hB]
  have hXl : ∀ l : Fin g, constantCoeff ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) = 0 :=
    fun l => constantCoeff_X _
  have hXr : ∀ l : Fin g, constantCoeff ((MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) = 0 :=
    fun l => constantCoeff_X _
  have hΦl : ∀ l, (subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (Φ.toPowerSeries l)).constantCoeff = 0 :=
    fun l => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXl) hXl (Φ.constantCoeff_eq_zero l)
  have hΦr : ∀ l, (subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (Φ.toPowerSeries l)).constantCoeff = 0 :=
    fun l => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXr) hXr (Φ.constantCoeff_eq_zero l)
  have hsw : (fun j => subst (Sum.elim
        (fun l => subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (Φ.toPowerSeries l))
        (fun l => subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (Φ.toPowerSeries l)))
        (F.toPowerSeries j)) =
      (fun j => subst (Sum.elim
        (fun l => subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (Φ.toPowerSeries l))
        (fun l => subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (Φ.toPowerSeries l)))
        (F.toPowerSeries j)) := funext fun j => MvFormalGroup.subst_elim_comm F hΦr hΦl j
  rw [key _ _ hXr hXl, hsw, ← key _ _ hXl hXr]

  have : (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))) = MvPowerSeries.X := by
    funext s; rcases s with l | l <;> rfl
  rw [this, MvPowerSeries.subst_self]
  rfl

end Generic

section SeriesHelpers
variable {R : Type*} [CommRing R]

theorem comp_addVia (F : MvFormalGroup 2 R) (s t φ : Series R)
    (hs : ∀ i, constantCoeff (s i) = 0) (ht : ∀ i, constantCoeff (t i) = 0) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    (Series.addVia F s t).comp φ = Series.addVia F (s.comp φ) (t.comp φ) := by
  funext i
  show subst φ (subst (Sum.elim s t) (F.toPowerSeries i)) = subst (Sum.elim (s.comp φ) (t.comp φ)) (F.toPowerSeries i)
  rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hs ht) (hasSubst_of_constantCoeff_zero hφ)]
  congr 1
  funext x
  rcases x with j | j <;> rfl

theorem hom_comp_addVia (F G : MvFormalGroup 2 R) (χ : F.Hom G) (s t : Series R)
    (hs : ∀ i, constantCoeff (s i) = 0) (ht : ∀ i, constantCoeff (t i) = 0) :
    Series.comp χ.toPowerSeries (Series.addVia F s t) = Series.addVia G (Series.comp χ.toPowerSeries s) (Series.comp χ.toPowerSeries t) := by
  funext i
  exact hom_subst_elim F G χ s t hs ht i

end SeriesHelpers

section Pullback
variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] (φ' : B' →+* B) (φ'' : B'' →+* B)
local notation "P" => ModuliPackage.pullbackRing φ' φ''
local notation "fst" => ModuliPackage.pullbackFst φ' φ''
local notation "snd" => ModuliPackage.pullbackSnd φ' φ''

theorem pullback_comm : φ'.comp fst = φ''.comp snd := RingHom.ext fun q => q.2

theorem pullback_ext {q q' : P} (h1 : fst q = fst q') (h2 : snd q = snd q') : q = q' :=
  Subtype.ext (Prod.ext h1 h2)

theorem pullback_hpb (a' : B') (a'' : B'') (h : φ' a' = φ'' a'') : ∃! b : P, fst b = a' ∧ snd b = a'' :=
  ⟨⟨(a', a''), h⟩, ⟨rfl, rfl⟩, fun q hq => pullback_ext φ' φ'' (hq.1.trans rfl) (hq.2.trans rfl)⟩

theorem mvPowerSeries_ext {σ : Type*} {u w : MvPowerSeries σ P}
    (h1 : MvPowerSeries.map fst u = MvPowerSeries.map fst w) (h2 : MvPowerSeries.map snd u = MvPowerSeries.map snd w) :
    u = w := by
  refine MvPowerSeries.ext fun n => pullback_ext φ' φ'' ?_ ?_
  · simpa only [MvPowerSeries.coeff_map] using congrArg (MvPowerSeries.coeff n) h1
  · simpa only [MvPowerSeries.coeff_map] using congrArg (MvPowerSeries.coeff n) h2

theorem series_ext {u w : Series P} (h1 : u.map fst = w.map fst) (h2 : u.map snd = w.map snd) : u = w :=
  funext fun i => mvPowerSeries_ext φ' φ'' (congrFun h1 i) (congrFun h2 i)

theorem isLocalHom_of_surjective_of_isNilpotent (hs : Function.Surjective φ'') (hn : IsNilpotent (RingHom.ker φ'')) :
    IsLocalHom φ'' := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b0, hb0⟩ := ha.exists_right_inv
  obtain ⟨b, rfl⟩ := hs b0
  have hmem : a * b - 1 ∈ RingHom.ker φ'' := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hb0, sub_self]
  obtain ⟨N, hN⟩ := hn
  have hnil : IsNilpotent (a * b - 1) := ⟨N, by
    have : (a * b - 1) ^ N ∈ RingHom.ker φ'' ^ N := Ideal.pow_mem_pow hmem N
    rw [hN] at this
    exact (Submodule.mem_bot _).mp this⟩
  have hu : IsUnit (a * b) := by
    have := hnil.isUnit_add_left_of_commute (isUnit_one) (Commute.one_right _)
    simpa using this
  exact isUnit_of_mul_isUnit_left hu

end Pullback
end OdGlue

theorem solution
    (p : ℕ) [Fact p.Prime] {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hs'' : Function.Surjective φ'') (hn'' : IsNilpotent (RingHom.ker φ''))
    (X' : FormalODModule p B') (X'' : FormalODModule p B'')
    (w : (X'.map φ').Hom (X''.map φ'')) (hw : w.IsIso) :
    ∃ (X : FormalODModule p (ModuliPackage.pullbackRing φ' φ''))
      (Ψ : (X.map (ModuliPackage.pullbackSnd φ' φ'')).Hom X''),
      X.map (ModuliPackage.pullbackFst φ' φ'') = X' ∧ Ψ.IsIso ∧ Ψ.toSeries.map φ'' = w.toSeries := by
  classical
  let fst := ModuliPackage.pullbackFst φ' φ''
  let snd := ModuliPackage.pullbackSnd φ' φ''
  have hcomm : φ'.comp fst = φ''.comp snd := OdGlue.pullback_comm φ' φ''
  haveI hloc : IsLocalHom φ'' := OdGlue.isLocalHom_of_surjective_of_isNilpotent φ'' hs'' hn''
  obtain ⟨wi, hwi1, hwi2⟩ := hw
  have ccw : ∀ i, constantCoeff (w.toSeries i) = 0 := w.isODHom.constantCoeff
  have ccwi : ∀ i, constantCoeff (wi.toSeries i) = 0 := wi.isODHom.constantCoeff
  have hvw : wi.toSeries.comp w.toSeries = Series.id B := congrArg FormalODModule.Hom.toSeries hwi1
  have hwv : w.toSeries.comp wi.toSeries = Series.id B := congrArg FormalODModule.Hom.toSeries hwi2

  have hunit : IsUnit (MvFormalGroup.linearPart w.toLawHom.toPowerSeries) := by
    have h1 := MvFormalGroup.linearPart_subst ccwi w.toSeries
    have h2 := MvFormalGroup.linearPart_subst ccw wi.toSeries
    rw [show (fun i => subst wi.toSeries (w.toSeries i)) = Series.id B from hwv] at h1
    rw [show (fun i => subst w.toSeries (wi.toSeries i)) = Series.id B from hvw] at h2
    rw [show Series.id B = fun i => MvPowerSeries.X i from rfl, MvFormalGroup.linearPart_X] at h1 h2
    exact ⟨⟨_, _, h1.symm, h2.symm⟩, rfl⟩
  have hLG := MvFormalGroup.exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective fst snd φ' φ'' hcomm (OdGlue.pullback_hpb φ' φ'') 2
  obtain ⟨G, Φh, Ψh, hG, hΨΦ, hΦΨ, hΦw⟩ := hLG.1 hs'' hloc X'.F X''.F w.toLawHom hunit
  have hglue2 := hLG.2

  have ccΦ : ∀ i, constantCoeff (Φh.toPowerSeries i) = 0 := Φh.constantCoeff_eq_zero
  have ccΨ : ∀ i, constantCoeff (Ψh.toPowerSeries i) = 0 := Ψh.constantCoeff_eq_zero
  have hΨΦs : Series.comp Ψh.toPowerSeries Φh.toPowerSeries = Series.id B'' :=
    congrArg MvFormalGroup.Hom.toPowerSeries hΨΦ
  have hΦΨs : Series.comp Φh.toPowerSeries Ψh.toPowerSeries = Series.id B'' :=
    congrArg MvFormalGroup.Hom.toPowerSeries hΦΨ
  have hΦw' : Series.map φ'' Φh.toPowerSeries = w.toSeries := funext hΦw
  have hΨw' : Series.map φ'' Ψh.toPowerSeries = wi.toSeries := by
    have h1 : (Series.map φ'' Ψh.toPowerSeries).comp w.toSeries = Series.id B := by
      rw [← hΦw', ← Series.map_comp _ _ _ ccΦ, hΨΦs, Series.map_id]
    have ccΨB : ∀ i, constantCoeff ((Series.map φ'' Ψh.toPowerSeries) i) = 0 := fun i => by
      show constantCoeff (MvPowerSeries.map φ'' _) = 0
      rw [MvPowerSeries.constantCoeff_map, ccΨ i, map_zero]
    calc Series.map φ'' Ψh.toPowerSeries = (Series.map φ'' Ψh.toPowerSeries).comp (Series.id B) := (Series.comp_id _).symm
      _ = (Series.map φ'' Ψh.toPowerSeries).comp (w.toSeries.comp wi.toSeries) := by rw [hwv]
      _ = ((Series.map φ'' Ψh.toPowerSeries).comp w.toSeries).comp wi.toSeries := by
          rw [Series.comp_assoc _ _ _ ccw ccwi]
      _ = wi.toSeries := by rw [h1, Series.id_comp _ ccwi]

  let T : Series B'' → Series B'' := fun s => Series.comp Ψh.toPowerSeries (s.comp Φh.toPowerSeries)
  have ccsΦ : ∀ s : Series B'', (∀ i, constantCoeff (s i) = 0) → ∀ i, constantCoeff ((s.comp Φh.toPowerSeries) i) = 0 :=
    fun s hs => Series.constantCoeff_comp hs ccΦ
  have ccT : ∀ s : Series B'', (∀ i, constantCoeff (s i) = 0) → ∀ i, constantCoeff (T s i) = 0 :=
    fun s hs => Series.constantCoeff_comp ccΨ (ccsΦ s hs)
  have hT_map : ∀ s : Series B'', (∀ i, constantCoeff (s i) = 0) →
      (T s).map φ'' = wi.toSeries.comp ((s.map φ'').comp w.toSeries) := by
    intro s hs
    show (Series.comp Ψh.toPowerSeries (s.comp Φh.toPowerSeries)).map φ'' = _
    rw [Series.map_comp _ _ _ (ccsΦ s hs), Series.map_comp _ _ _ ccΦ, hΨw', hΦw']
  have hT_id : T (Series.id B'') = Series.id B'' := by
    show Series.comp Ψh.toPowerSeries ((Series.id _).comp Φh.toPowerSeries) = _
    rw [Series.id_comp _ ccΦ, hΨΦs]
  have hT_comp : ∀ s t : Series B'', (∀ i, constantCoeff (s i) = 0) → (∀ i, constantCoeff (t i) = 0) →
      T (s.comp t) = (T s).comp (T t) := by
    intro s t hs ht
    show Series.comp Ψh.toPowerSeries ((s.comp t).comp Φh.toPowerSeries) =
      (Series.comp Ψh.toPowerSeries (s.comp Φh.toPowerSeries)).comp (Series.comp Ψh.toPowerSeries (t.comp Φh.toPowerSeries))
    rw [Series.comp_assoc _ _ _ (ccsΦ s hs) (ccT t ht), Series.comp_assoc s _ _ ccΦ (ccT t ht),
      ← Series.comp_assoc Φh.toPowerSeries _ _ ccΨ (ccsΦ t ht), hΦΨs, Series.id_comp _ (ccsΦ t ht),
      Series.comp_assoc s t _ ht ccΦ]
  have hT_addVia : ∀ s t : Series B'', (∀ i, constantCoeff (s i) = 0) → (∀ i, constantCoeff (t i) = 0) →
      T (Series.addVia X''.F s t) = Series.addVia (G.map snd) (T s) (T t) := by
    intro s t hs ht
    show Series.comp Ψh.toPowerSeries ((Series.addVia X''.F s t).comp Φh.toPowerSeries) = _
    rw [OdGlue.comp_addVia X''.F s t _ hs ht ccΦ,
      OdGlue.hom_comp_addVia X''.F (G.map snd) Ψh _ _ (ccsΦ s hs) (ccsΦ t ht)]

  have hagree : ∀ (s' : Series B') (s'' : Series B''), (∀ i, constantCoeff (s' i) = 0) → (∀ i, constantCoeff (s'' i) = 0) →
      w.toSeries.comp (s'.map φ') = (s''.map φ'').comp w.toSeries →
      ∀ i, MvPowerSeries.map φ' (s' i) = MvPowerSeries.map φ'' (T s'' i) := by
    intro s' s'' hs' hs'' hws i
    have ccs'B : ∀ i, constantCoeff ((s'.map φ') i) = 0 := fun i => by
      show constantCoeff (MvPowerSeries.map φ' _) = 0
      rw [MvPowerSeries.constantCoeff_map, hs' i, map_zero]
    have key : (T s'').map φ'' = s'.map φ' := by
      rw [hT_map s'' hs'', ← hws, ← Series.comp_assoc _ _ _ ccw ccs'B, hvw, Series.id_comp _ ccs'B]
    exact (congrFun key i).symm

  have hla : ∀ a, IsLawHom (G.map fst) (G.map fst) (X'.act a) := fun a => by rw [hG]; exact X'.isLawHom_act a
  have hlv : IsLawHom (G.map fst) (G.map fst) X'.varpi := by rw [hG]; exact X'.isLawHom_varpi
  have hact : ∀ a, ∃ α : G.Hom G, (∀ i, MvPowerSeries.map fst (α.toPowerSeries i) = X'.act a i) ∧
      (∀ i, MvPowerSeries.map snd (α.toPowerSeries i) = T (X''.act a) i) := fun a =>
    (hglue2 G G (hla a).toHom (Ψh.comp ((X''.isLawHom_act a).toHom.comp Φh))
      (hagree _ _ (X'.isLawHom_act a).1 (X''.isLawHom_act a).1 (w.isODHom.2.1 a))).exists
  choose α hα1 hα2 using hact
  obtain ⟨β, ⟨hβ1, hβ2⟩, -⟩ := hglue2 G G hlv.toHom (Ψh.comp (X''.isLawHom_varpi.toHom.comp Φh))
      (hagree _ _ X'.isLawHom_varpi.1 X''.isLawHom_varpi.1 w.isODHom.2.2)
  have hα1' : ∀ a, Series.map fst (α a).toPowerSeries = X'.act a := fun a => funext (hα1 a)
  have hα2' : ∀ a, Series.map snd (α a).toPowerSeries = T (X''.act a) := fun a => funext (hα2 a)
  have hβ1' : Series.map fst β.toPowerSeries = X'.varpi := funext hβ1
  have hβ2' : Series.map snd β.toPowerSeries = T X''.varpi := funext hβ2
  have ccα : ∀ a i, constantCoeff ((α a).toPowerSeries i) = 0 := fun a => (α a).constantCoeff_eq_zero
  have ccβ : ∀ i, constantCoeff (β.toPowerSeries i) = 0 := β.constantCoeff_eq_zero
  have cca'' : ∀ a i, constantCoeff (X''.act a i) = 0 := fun a => (X''.isLawHom_act a).1
  have ccv'' : ∀ i, constantCoeff (X''.varpi i) = 0 := X''.isLawHom_varpi.1

  haveI : X''.F.IsComm := X''.isComm
  have hGfst_comm : (G.map fst).IsComm := by rw [hG]; exact X'.isComm
  have hGsnd_comm : (G.map snd).IsComm := OdGlue.isComm_of_hom_of_comp_eq_id X''.F (G.map snd) Φh Ψh hΨΦ
  have hGcomm : G.IsComm := by
    refine ⟨fun i => OdGlue.mvPowerSeries_ext φ' φ'' ?_ ?_⟩
    · have := hGfst_comm.comm i
      rw [map_subst (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X]))]
      convert this using 2
      funext s; rcases s with j | j <;> simp [MvPowerSeries.map_X]
      all_goals rfl
    · have := hGsnd_comm.comm i
      rw [map_subst (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X]))]
      convert this using 2
      funext s; rcases s with j | j <;> simp [MvPowerSeries.map_X]
      all_goals rfl

  let X : FormalODModule p (ModuliPackage.pullbackRing φ' φ'') :=
    { F := G
      isComm := hGcomm
      act := fun a => (α a).toPowerSeries
      varpi := β.toPowerSeries
      isLawHom_act := fun a => IsLawHom.of_hom (α a)
      isLawHom_varpi := IsLawHom.of_hom β
      act_one := by
        apply OdGlue.series_ext φ' φ''
        · rw [hα1', X'.act_one, Series.map_id]
        · rw [hα2', X''.act_one, hT_id, Series.map_id]
      act_mul := fun a b => by
        apply OdGlue.series_ext φ' φ''
        · rw [hα1', Series.map_comp _ _ _ (ccα b), hα1', hα1', X'.act_mul]
        · rw [hα2', Series.map_comp _ _ _ (ccα b), hα2', hα2', X''.act_mul, hT_comp _ _ (cca'' a) (cca'' b)]
      act_add := fun a b => by
        apply OdGlue.series_ext φ' φ''
        · rw [hα1', Series.map_addVia _ _ _ _ (ccα a) (ccα b), hα1', hα1', hG, X'.act_add]
        · rw [hα2', Series.map_addVia _ _ _ _ (ccα a) (ccα b), hα2', hα2', X''.act_add,
            hT_addVia _ _ (cca'' a) (cca'' b)]
      varpi_comp_varpi := by
        apply OdGlue.series_ext φ' φ''
        · rw [Series.map_comp _ _ _ ccβ, hβ1', hα1', X'.varpi_comp_varpi]
        · rw [Series.map_comp _ _ _ ccβ, hβ2', hα2', ← hT_comp _ _ ccv'' ccv'', X''.varpi_comp_varpi]
      varpi_comp_act := fun a => by
        apply OdGlue.series_ext φ' φ''
        · rw [Series.map_comp _ _ _ (ccα a), Series.map_comp _ _ _ ccβ, hβ1', hα1', hα1', X'.varpi_comp_act]
        · rw [Series.map_comp _ _ _ (ccα a), Series.map_comp _ _ _ ccβ, hβ2', hα2', hα2',
            ← hT_comp _ _ ccv'' (cca'' a), X''.varpi_comp_act, hT_comp _ _ (cca'' _) ccv''] }

  have hΦOD : FormalODModule.IsODHom (X.map snd) X'' Φh.toPowerSeries := by
    refine ⟨IsLawHom.of_hom Φh, fun a => ?_, ?_⟩
    · show Series.comp Φh.toPowerSeries ((Series.map snd (α a).toPowerSeries)) = (X''.act a).comp Φh.toPowerSeries
      rw [hα2', show T (X''.act a) = Series.comp Ψh.toPowerSeries ((X''.act a).comp Φh.toPowerSeries) from rfl,
        ← Series.comp_assoc _ _ _ ccΨ (ccsΦ _ (cca'' a)), hΦΨs, Series.id_comp _ (ccsΦ _ (cca'' a))]
    · show Series.comp Φh.toPowerSeries ((Series.map snd β.toPowerSeries)) = X''.varpi.comp Φh.toPowerSeries
      rw [hβ2', show T X''.varpi = Series.comp Ψh.toPowerSeries (X''.varpi.comp Φh.toPowerSeries) from rfl,
        ← Series.comp_assoc _ _ _ ccΨ (ccsΦ _ ccv''), hΦΨs, Series.id_comp _ (ccsΦ _ ccv'')]
  have hΨOD : FormalODModule.IsODHom X'' (X.map snd) Ψh.toPowerSeries := by
    refine ⟨IsLawHom.of_hom Ψh, fun a => ?_, ?_⟩
    · show Series.comp Ψh.toPowerSeries (X''.act a) = (Series.map snd (α a).toPowerSeries).comp Ψh.toPowerSeries
      rw [hα2', show T (X''.act a) = Series.comp Ψh.toPowerSeries ((X''.act a).comp Φh.toPowerSeries) from rfl,
        Series.comp_assoc _ _ _ (ccsΦ _ (cca'' a)) ccΨ, Series.comp_assoc _ _ _ ccΦ ccΨ, hΦΨs, Series.comp_id]
    · show Series.comp Ψh.toPowerSeries X''.varpi = (Series.map snd β.toPowerSeries).comp Ψh.toPowerSeries
      rw [hβ2', show T X''.varpi = Series.comp Ψh.toPowerSeries (X''.varpi.comp Φh.toPowerSeries) from rfl,
        Series.comp_assoc _ _ _ (ccsΦ _ ccv'') ccΨ, Series.comp_assoc _ _ _ ccΦ ccΨ, hΦΨs, Series.comp_id]
  refine ⟨X, ⟨Φh.toPowerSeries, hΦOD⟩, ?_, ⟨⟨Ψh.toPowerSeries, hΨOD⟩, ?_, ?_⟩, hΦw'⟩
  · exact FormalODModule.ext' hG (funext hα1') hβ1'
  · exact FormalODModule.Hom.ext hΨΦs
  · exact FormalODModule.Hom.ext hΦΨs

#print axioms solution

end S_CerednikDrinfeld_FormalODModule_exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso (solution)
