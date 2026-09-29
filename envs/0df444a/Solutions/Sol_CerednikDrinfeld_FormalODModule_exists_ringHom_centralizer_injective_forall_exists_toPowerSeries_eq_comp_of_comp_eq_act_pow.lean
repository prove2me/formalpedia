-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/efc1fa44-aa10-5579-8011-f7979f318d5a

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff subst_comp_subst_apply subst_X
  coe_substAlgHom constantCoeff_subst_eq_zero)

noncomputable section

namespace ADT

section SeriesAlgebra

variable {k : Type} [CommRing k]

theorem zero_comp (φ : Series k) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    Series.comp (fun _ => (0 : MvPowerSeries (Fin 2) k)) φ = fun _ => 0 := by
  funext i
  show subst φ (0 : MvPowerSeries (Fin 2) k) = 0
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero hφ), map_zero]

theorem comp_zero (φ : Series k) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    φ.comp (fun _ => (0 : MvPowerSeries (Fin 2) k)) = fun _ => 0 := by
  funext i
  exact MvFormalGroup.subst_zero_of_constantCoeff_eq_zero (hφ i)

theorem addVia_comp (G : MvFormalGroup 2 k) (φ ψ χ : Series k)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) (hχ : ∀ i, constantCoeff (χ i) = 0) :
    (Series.addVia G φ ψ).comp χ = Series.addVia G (φ.comp χ) (ψ.comp χ) := by
  funext i
  show subst χ (subst (Sum.elim φ ψ) (G.toPowerSeries i)) =
    subst (Sum.elim (fun j => subst χ (φ j)) (fun j => subst χ (ψ j))) (G.toPowerSeries i)
  rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hφ hψ) (hasSubst_of_constantCoeff_zero hχ)]
  congr 1
  funext s
  rcases s with j | j <;> rfl

theorem comp_addVia {F G : MvFormalGroup 2 k} (β : Series k) (hβ : IsLawHom F G β) (φ ψ : Series k)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    β.comp (Series.addVia F φ ψ) = Series.addVia G (β.comp φ) (β.comp ψ) := by
  funext i
  show subst (fun j => subst (Sum.elim φ ψ) (F.toPowerSeries j)) (β i) =
    subst (Sum.elim (fun j => subst φ (β j)) (fun j => subst ψ (β j))) (G.toPowerSeries i)
  have hbc : HasSubst (Sum.elim φ ψ) := MvFormalGroup.hasSubst_elim hφ hψ
  have hXl : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _
  have hXr : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _
  have haLR : HasSubst (Sum.elim
      (fun j => subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (β j))
      fun j => subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (β j)) :=
    MvFormalGroup.hasSubst_elim
      (fun j => constantCoeff_subst_eq_zero hXl (fun l => MvPowerSeries.constantCoeff_X _) (hβ.1 j))
      (fun j => constantCoeff_subst_eq_zero hXr (fun l => MvPowerSeries.constantCoeff_X _) (hβ.1 j))
  rw [← subst_comp_subst_apply F.hasSubst_toPowerSeries hbc, hβ.2 i, subst_comp_subst_apply haLR hbc]
  congr 1
  funext s
  rcases s with j | j
  · show subst (Sum.elim φ ψ) (subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (β j)) =
      subst φ (β j)
    rw [subst_comp_subst_apply hXl hbc]
    congr 1
    funext l
    exact subst_X hbc (Sum.inl l)
  · show subst (Sum.elim φ ψ) (subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (β j)) =
      subst ψ (β j)
    rw [subst_comp_subst_apply hXr hbc]
    congr 1
    funext l
    exact subst_X hbc (Sum.inr l)

end SeriesAlgebra

section Main

variable {r : ℕ} [Fact r.Prime] {k₀ k : Type} [CommRing k₀] [CommRing k] (κ : k₀ →+* k)
  (X₀ : FormalODModule r k₀) (Φ : FormalODModule r k) (β₀ β₀' : Series k) (N : ℕ)
  (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
  (h₁ : β₀'.comp β₀ = Φ.act ((r : Zp2 r) ^ N)) (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N))

def kap (ε : MvFormalGroup.End X₀.F) : Series k := Series.map κ ε.toPowerSeries

theorem kap_cc (ε : MvFormalGroup.End X₀.F) : ∀ i, constantCoeff (kap κ X₀ ε i) = 0 := fun i => by
  show constantCoeff (MvPowerSeries.map κ (ε.toPowerSeries i)) = 0
  rw [MvPowerSeries.constantCoeff_map, ε.constantCoeff_eq_zero i, map_zero]

theorem kap_isLawHom (ε : MvFormalGroup.End X₀.F) : IsLawHom (X₀.map κ).F (X₀.map κ).F (kap κ X₀ ε) :=
  (IsLawHom.of_hom ε).map κ

theorem act_cc (a : Zp2 r) : ∀ i, constantCoeff (Φ.act a i) = 0 := (Φ.isLawHom_act a).1
theorem varpi_cc : ∀ i, constantCoeff (Φ.varpi i) = 0 := Φ.isLawHom_varpi.1

theorem kap_comm_act (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (a : Zp2 r) :
    ((X₀.map κ).act a).comp (kap κ X₀ ε) = (kap κ X₀ ε).comp ((X₀.map κ).act a) := by
  have h := Subring.mem_centralizer_iff.mp ε.2 (X₀.actEnd a) (Set.mem_union_left _ ⟨a, rfl⟩)
  have h' : Series.comp (X₀.act a) (ε : MvFormalGroup.End X₀.F).toPowerSeries =
      Series.comp (ε : MvFormalGroup.End X₀.F).toPowerSeries (X₀.act a) :=
    congrArg MvFormalGroup.Hom.toPowerSeries h
  have h'' := congrArg (Series.map κ) h'
  rw [Series.map_comp κ _ _ (ε : MvFormalGroup.End X₀.F).constantCoeff_eq_zero,
    Series.map_comp κ _ _ (X₀.isLawHom_act a).1] at h''
  rw [FormalODModule.map_act]
  exact h''

theorem kap_comm_varpi (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :
    (X₀.map κ).varpi.comp (kap κ X₀ ε) = (kap κ X₀ ε).comp (X₀.map κ).varpi := by
  have h := Subring.mem_centralizer_iff.mp ε.2 X₀.varpiEnd (Set.mem_union_right _ (Set.mem_singleton _))
  have h' : Series.comp X₀.varpi (ε : MvFormalGroup.End X₀.F).toPowerSeries =
      Series.comp (ε : MvFormalGroup.End X₀.F).toPowerSeries X₀.varpi :=
    congrArg MvFormalGroup.Hom.toPowerSeries h
  have h'' := congrArg (Series.map κ) h'
  rw [Series.map_comp κ _ _ (ε : MvFormalGroup.End X₀.F).constantCoeff_eq_zero,
    Series.map_comp κ _ _ X₀.isLawHom_varpi.1] at h''
  rw [FormalODModule.map_varpi]
  exact h''

def adSer (ε : MvFormalGroup.End X₀.F) : Series k := β₀'.comp ((kap κ X₀ ε).comp β₀)

include hβ₀ hβ₀' in
theorem adSer_isLawHom (ε : MvFormalGroup.End X₀.F) : IsLawHom Φ.F Φ.F (adSer κ X₀ β₀ β₀' ε) :=
  hβ₀'.1.comp ((kap_isLawHom κ X₀ ε).comp hβ₀.1)

def adEnd (ε : MvFormalGroup.End X₀.F) : MvFormalGroup.End Φ.F := (adSer_isLawHom κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε).toHom

theorem adEnd_toPowerSeries (ε : MvFormalGroup.End X₀.F) :
    (adEnd κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε).toPowerSeries = adSer κ X₀ β₀ β₀' ε := rfl

include hβ₀ hβ₀' in

theorem adSer_comm (ε : MvFormalGroup.End X₀.F) (sΦ sY : Series k)
    (hsΦ : ∀ i, constantCoeff (sΦ i) = 0) (hsY : ∀ i, constantCoeff (sY i) = 0)
    (i1 : β₀'.comp sY = sΦ.comp β₀') (i2 : sY.comp (kap κ X₀ ε) = (kap κ X₀ ε).comp sY)
    (i3 : β₀.comp sΦ = sY.comp β₀) :
    sΦ.comp (adSer κ X₀ β₀ β₀' ε) = (adSer κ X₀ β₀ β₀' ε).comp sΦ := by
  have cβ := hβ₀.constantCoeff
  have cβ' := hβ₀'.constantCoeff
  have cκ := kap_cc κ X₀ ε
  unfold adSer
  calc sΦ.comp (β₀'.comp ((kap κ X₀ ε).comp β₀))
      = (sΦ.comp β₀').comp ((kap κ X₀ ε).comp β₀) := by
        rw [Series.comp_assoc _ _ _ cβ' (Series.constantCoeff_comp cκ cβ)]
    _ = (β₀'.comp sY).comp ((kap κ X₀ ε).comp β₀) := by rw [i1]
    _ = β₀'.comp ((sY.comp (kap κ X₀ ε)).comp β₀) := by
        rw [Series.comp_assoc _ _ _ hsY (Series.constantCoeff_comp cκ cβ),
          ← Series.comp_assoc _ _ _ cκ cβ]
    _ = β₀'.comp (((kap κ X₀ ε).comp sY).comp β₀) := by rw [i2]
    _ = β₀'.comp ((kap κ X₀ ε).comp (β₀.comp sΦ)) := by
        rw [Series.comp_assoc _ _ _ hsY cβ, ← i3]
    _ = (β₀'.comp ((kap κ X₀ ε).comp β₀)).comp sΦ := by
        rw [← Series.comp_assoc _ _ _ cβ hsΦ, ← Series.comp_assoc _ _ _ (Series.constantCoeff_comp cκ cβ) hsΦ]

include hβ₀ hβ₀' in
theorem adEnd_mem (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :
    adEnd κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε ∈ Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) := by
  rw [Subring.mem_centralizer_iff]
  rintro s (⟨a, rfl⟩ | hs)
  · apply MvFormalGroup.Hom.ext
    show (Φ.act a).comp (adSer κ X₀ β₀ β₀' ε) = (adSer κ X₀ β₀ β₀' ε).comp (Φ.act a)
    exact adSer_comm κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε (Φ.act a) ((X₀.map κ).act a) (act_cc Φ a) ((X₀.map κ).isLawHom_act a).1
      (hβ₀'.2.1 a) (kap_comm_act κ X₀ ε a) (hβ₀.2.1 a)
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    apply MvFormalGroup.Hom.ext
    show Φ.varpi.comp (adSer κ X₀ β₀ β₀' ε) = (adSer κ X₀ β₀ β₀' ε).comp Φ.varpi
    exact adSer_comm κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε Φ.varpi (X₀.map κ).varpi (varpi_cc Φ) (X₀.map κ).isLawHom_varpi.1
      hβ₀'.2.2 (kap_comm_varpi κ X₀ ε) hβ₀.2.2

def ad (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :
    ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) :=
  ⟨adEnd κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε, adEnd_mem κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε⟩

theorem ad_toPowerSeries (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :
    ((ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) :
      MvFormalGroup.End Φ.F).toPowerSeries = adSer κ X₀ β₀ β₀' (ε : MvFormalGroup.End X₀.F) := rfl

theorem natCast_toPowerSeries (n : ℕ) :
    (((n : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) : MvFormalGroup.End Φ.F)).toPowerSeries =
      Φ.act (n : Zp2 r) := by
  rw [SubringClass.coe_natCast, MvFormalGroup.End.toPowerSeries_natCast, FormalODModule.act_natCast]

theorem rpow_toPowerSeries :
    ((((r ^ N : ℕ) : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) : MvFormalGroup.End Φ.F).toPowerSeries =
      Φ.act ((r : Zp2 r) ^ N) := by
  rw [natCast_toPowerSeries, Nat.cast_pow]

include h₁ in
theorem ad_one : ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' 1 = ((r ^ N : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) := by
  apply Subtype.ext
  apply MvFormalGroup.Hom.ext
  rw [ad_toPowerSeries, rpow_toPowerSeries, ← h₁]
  show β₀'.comp ((Series.map κ (MvFormalGroup.Hom.toPowerSeries (1 : MvFormalGroup.End X₀.F))).comp β₀) = β₀'.comp β₀
  rw [MvFormalGroup.End.toPowerSeries_one]
  change β₀'.comp (((Series.id k₀).map κ).comp β₀) = β₀'.comp β₀
  rw [Series.map_id, Series.id_comp β₀ hβ₀.constantCoeff]

include h₂ in
theorem ad_mul (ε₁ ε₂ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :
    ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε₁ * ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε₂ =
      ((r ^ N : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) * ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' (ε₁ * ε₂) := by
  apply Subtype.ext
  apply MvFormalGroup.Hom.ext
  show Series.comp (adSer κ X₀ β₀ β₀' ε₁) (adSer κ X₀ β₀ β₀' ε₂) =
    Series.comp (MvFormalGroup.Hom.toPowerSeries ((((r ^ N : ℕ) : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) :
      MvFormalGroup.End Φ.F)) (adSer κ X₀ β₀ β₀' ((ε₁ * ε₂ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) : MvFormalGroup.End X₀.F))
  rw [rpow_toPowerSeries]
  have cβ := hβ₀.constantCoeff
  have cβ' := hβ₀'.constantCoeff
  have c1 := kap_cc κ X₀ (ε₁ : MvFormalGroup.End X₀.F)
  have c2 := kap_cc κ X₀ (ε₂ : MvFormalGroup.End X₀.F)
  have cP : ∀ i, constantCoeff ((X₀.map κ).act ((r : Zp2 r) ^ N) i) = 0 := ((X₀.map κ).isLawHom_act _).1
  have hk : kap κ X₀ ((ε₁ * ε₂ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) : MvFormalGroup.End X₀.F) =
      (kap κ X₀ ε₁).comp (kap κ X₀ ε₂) := by
    show Series.map κ (Series.comp (ε₁ : MvFormalGroup.End X₀.F).toPowerSeries (ε₂ : MvFormalGroup.End X₀.F).toPowerSeries) = _
    exact Series.map_comp κ _ _ (ε₂ : MvFormalGroup.End X₀.F).constantCoeff_eq_zero
  unfold adSer
  rw [hk]

  calc (β₀'.comp ((kap κ X₀ ε₁).comp β₀)).comp (β₀'.comp ((kap κ X₀ ε₂).comp β₀))
      = β₀'.comp ((kap κ X₀ ε₁).comp ((β₀.comp β₀').comp ((kap κ X₀ ε₂).comp β₀))) := by
        rw [Series.comp_assoc _ _ _ (Series.constantCoeff_comp c1 cβ) (Series.constantCoeff_comp cβ' (Series.constantCoeff_comp c2 cβ)),
          Series.comp_assoc _ _ _ cβ (Series.constantCoeff_comp cβ' (Series.constantCoeff_comp c2 cβ)),
          ← Series.comp_assoc β₀ β₀' _ cβ' (Series.constantCoeff_comp c2 cβ)]
    _ = β₀'.comp ((kap κ X₀ ε₁).comp (((X₀.map κ).act ((r : Zp2 r) ^ N)).comp ((kap κ X₀ ε₂).comp β₀))) := by rw [h₂]
    _ = β₀'.comp ((((X₀.map κ).act ((r : Zp2 r) ^ N)).comp (kap κ X₀ ε₁)).comp ((kap κ X₀ ε₂).comp β₀)) := by
        rw [← Series.comp_assoc _ _ _ cP (Series.constantCoeff_comp c2 cβ), ← kap_comm_act κ X₀ ε₁]
    _ = (β₀'.comp ((X₀.map κ).act ((r : Zp2 r) ^ N))).comp ((kap κ X₀ ε₁).comp ((kap κ X₀ ε₂).comp β₀)) := by
        rw [Series.comp_assoc _ _ _ c1 (Series.constantCoeff_comp c2 cβ),
          ← Series.comp_assoc β₀' _ _ cP (Series.constantCoeff_comp c1 (Series.constantCoeff_comp c2 cβ))]
    _ = (Φ.act ((r : Zp2 r) ^ N)).comp (β₀'.comp (((kap κ X₀ ε₁).comp (kap κ X₀ ε₂)).comp β₀)) := by
        rw [hβ₀'.2.1, Series.comp_assoc _ _ _ cβ' (Series.constantCoeff_comp c1 (Series.constantCoeff_comp c2 cβ)),
          Series.comp_assoc _ _ _ c2 cβ]

theorem ad_add (ε₁ ε₂ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :
    ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' (ε₁ + ε₂) = ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε₁ + ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε₂ := by
  apply Subtype.ext
  apply MvFormalGroup.Hom.ext
  show adSer κ X₀ β₀ β₀' ((ε₁ + ε₂ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) : MvFormalGroup.End X₀.F) =
    Series.addVia Φ.F (adSer κ X₀ β₀ β₀' ε₁) (adSer κ X₀ β₀ β₀' ε₂)
  have cβ := hβ₀.constantCoeff
  have c1 := kap_cc κ X₀ (ε₁ : MvFormalGroup.End X₀.F)
  have c2 := kap_cc κ X₀ (ε₂ : MvFormalGroup.End X₀.F)
  have hk : kap κ X₀ ((ε₁ + ε₂ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) : MvFormalGroup.End X₀.F) =
      Series.addVia (X₀.map κ).F (kap κ X₀ ε₁) (kap κ X₀ ε₂) := by
    show Series.map κ (Series.addVia X₀.F (ε₁ : MvFormalGroup.End X₀.F).toPowerSeries (ε₂ : MvFormalGroup.End X₀.F).toPowerSeries) = _
    rw [Series.map_addVia κ X₀.F _ _ (ε₁ : MvFormalGroup.End X₀.F).constantCoeff_eq_zero (ε₂ : MvFormalGroup.End X₀.F).constantCoeff_eq_zero]
    rfl
  unfold adSer
  rw [hk, addVia_comp _ _ _ _ c1 c2 cβ,
    comp_addVia β₀' hβ₀'.1 _ _ (Series.constantCoeff_comp c1 cβ) (Series.constantCoeff_comp c2 cβ)]

theorem ad_zero : ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' 0 = 0 := by
  apply Subtype.ext
  apply MvFormalGroup.Hom.ext
  show adSer κ X₀ β₀ β₀' ((0 : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) : MvFormalGroup.End X₀.F) = fun _ => 0
  have hk : kap κ X₀ ((0 : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) : MvFormalGroup.End X₀.F) = fun _ => 0 := by
    funext i
    show MvPowerSeries.map κ (0 : MvPowerSeries (Fin 2) k₀) = 0
    exact map_zero _
  unfold adSer
  rw [hk, zero_comp β₀ hβ₀.constantCoeff, comp_zero β₀' hβ₀'.constantCoeff]

include hβ₀ hβ₀' h₂ in
theorem beta_comp_adSer (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :
    β₀.comp (adSer κ X₀ β₀ β₀' ε) = ((kap κ X₀ ε).comp β₀).comp (Φ.act ((r : Zp2 r) ^ N)) := by
  have cβ := hβ₀.constantCoeff
  have cβ' := hβ₀'.constantCoeff
  have cκ := kap_cc κ X₀ (ε : MvFormalGroup.End X₀.F)
  have cP : ∀ i, constantCoeff ((X₀.map κ).act ((r : Zp2 r) ^ N) i) = 0 := ((X₀.map κ).isLawHom_act _).1
  unfold adSer
  rw [← Series.comp_assoc _ _ _ cβ' (Series.constantCoeff_comp cκ cβ), h₂,
    ← Series.comp_assoc _ _ _ cκ cβ, kap_comm_act κ X₀ ε, Series.comp_assoc _ _ _ cP cβ, ← hβ₀.2.1,
    ← Series.comp_assoc _ _ _ cβ (act_cc Φ _)]

include h₂ in
theorem eq_zero_of_ad_eq_zero (hκ : Function.Injective κ)
    (hc₁ : ∀ σ τ : Series k, σ.comp β₀ = τ.comp β₀ → σ = τ)
    (hc₂ : ∀ σ τ : Series k, σ.comp (Φ.act ((r : Zp2 r) ^ N)) = τ.comp (Φ.act ((r : Zp2 r) ^ N)) → σ = τ)
    (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})))
    (h : ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε = 0) : ε = 0 := by
  have h1 : adSer κ X₀ β₀ β₀' ε = fun _ => 0 := by
    have := congrArg (fun x : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) => (x : MvFormalGroup.End Φ.F).toPowerSeries) h
    exact this
  have h2 : ((kap κ X₀ ε).comp β₀).comp (Φ.act ((r : Zp2 r) ^ N)) =
      Series.comp (fun _ => (0 : MvPowerSeries (Fin 2) k)) (Φ.act ((r : Zp2 r) ^ N)) := by
    rw [← beta_comp_adSer κ X₀ Φ β₀ β₀' N hβ₀ hβ₀' h₂ ε, h1, comp_zero β₀ hβ₀.constantCoeff, zero_comp _ (act_cc Φ _)]
  have h3 : (kap κ X₀ ε).comp β₀ = Series.comp (fun _ => (0 : MvPowerSeries (Fin 2) k)) β₀ := by
    rw [hc₂ _ _ h2, zero_comp _ hβ₀.constantCoeff]
  have h4 : kap κ X₀ ε = fun _ => 0 := hc₁ _ _ h3
  apply Subtype.ext
  apply MvFormalGroup.Hom.ext
  funext i
  show (ε : MvFormalGroup.End X₀.F).toPowerSeries i = 0
  have h5 : MvPowerSeries.map κ ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) = 0 := congrFun h4 i
  ext n
  apply hκ
  rw [← MvPowerSeries.coeff_map, h5, map_zero, map_zero, map_zero]

end Main

end ADT

open ADT in
theorem solution
    {r : ℕ} [Fact r.Prime]
    {k₀ k : Type} [CommRing k₀] [CommRing k] (κ : k₀ →+* k) (hκ : Function.Injective κ)
    (X₀ : FormalODModule r k₀) (Φ : FormalODModule r k)
    (β₀ β₀' : SpecialFormal.Series k) (N : ℕ)
    (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (h₁ : β₀'.comp β₀ = Φ.act ((r : Zp2 r) ^ N)) (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N))
    (hc₁ : ∀ σ τ : SpecialFormal.Series k, σ.comp β₀ = τ.comp β₀ → σ = τ)
    (hc₂ : ∀ σ τ : SpecialFormal.Series k, σ.comp (Φ.act ((r : Zp2 r) ^ N)) = τ.comp (Φ.act ((r : Zp2 r) ^ N)) → σ = τ)
    {K₀ : Type} [Field K₀] [CharZero K₀]
    (E₀ : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀) :
    ∃ E : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀,
      Function.Injective E ∧
      ∀ ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
        ∃ e : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})),
          (e : MvFormalGroup.End Φ.F).toPowerSeries =
            β₀'.comp ((SpecialFormal.Series.map κ (ε : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
          E₀ e = ((r : K₀) ^ N) • E ε  := by
  classical
  have hr : ((r : K₀) ^ N) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero)
  set c : K₀ := ((r : K₀) ^ N)⁻¹ with hc
  have hcr : c * (r : K₀) ^ N = 1 := inv_mul_cancel₀ hr

  have hE₀r : E₀ ((r ^ N : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) =
      ((r : K₀) ^ N) • (1 : Matrix (Fin 2) (Fin 2) K₀) := by
    rw [map_natCast, ← map_natCast (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)), Algebra.algebraMap_eq_smul_one,
      Nat.cast_pow]
  let E : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀ :=
    { toFun := fun ε => c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε)
      map_one' := by
        show c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' 1) = 1
        rw [ad_one κ X₀ Φ β₀ β₀' N hβ₀ hβ₀' h₁, hE₀r, smul_smul, hcr, one_smul]
      map_mul' := fun x y => by
        show c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' (x * y)) =
          (c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' x)) * (c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' y))
        rw [smul_mul_smul_comm, ← map_mul, ad_mul κ X₀ Φ β₀ β₀' N hβ₀ hβ₀' h₂, map_mul, hE₀r, smul_one_mul,
          smul_smul, mul_assoc, hcr, mul_one]
      map_zero' := by
        show c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' 0) = 0
        rw [ad_zero, map_zero, smul_zero]
      map_add' := fun x y => by
        show c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' (x + y)) =
          c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' x) + c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' y)
        rw [ad_add, map_add, smul_add] }
  refine ⟨E, ?_, fun ε => ⟨ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε, rfl, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro ε hε
    have h0 : E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε) = 0 := by
      have : c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε) = 0 := hε
      exact (smul_eq_zero.mp this).resolve_left (inv_ne_zero hr)
    have had : ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε = 0 := hE₀ (by rw [h0, map_zero])
    exact eq_zero_of_ad_eq_zero κ X₀ Φ β₀ β₀' N hβ₀ hβ₀' h₂ hκ hc₁ hc₂ ε had
  · show E₀ _ = ((r : K₀) ^ N) • (c • E₀ (ad κ X₀ Φ β₀ β₀' hβ₀ hβ₀' ε))
    rw [smul_smul, mul_comm, hcr, one_smul]

end
end S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow (solution)
