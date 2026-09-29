-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_map_of_hasStructureConstants_of_map_eq_of_mul_eq_of_ker_mul_ker_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/639bf38c-6edf-553f-b031-6a9452a19572

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_hasStructureConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_map_of_surjective_of_isNilpotent_ker
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_id
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent

import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_span_range_eq
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_of_hasStructureConstants_of_map_eq_of_mul_eq_of_ker_mul_ker_eq_bot
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"
set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open MvPowerSeries

namespace ReduceF1A2

theorem span_range_id_eq (B : Type) [CommRing B] :
    Ideal.span (Set.range (Series.id B)) = Ideal.span {(X 0 : MvPowerSeries (Fin 2) B), X 1} := by
  congr 1
  ext f
  simp only [Set.mem_range, Series.id, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

theorem mem_span_range_id_iff {B : Type} [CommRing B] (f : MvPowerSeries (Fin 2) B) :
    f ∈ Ideal.span (Set.range (Series.id B)) ↔ constantCoeff f = 0 := by
  rw [span_range_id_eq, ← pow_one (Ideal.span _),
    MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt B 1 f]
  constructor
  · intro h
    have := h 0 (by simp)
    simpa using this
  · intro h n hn
    have hn0 : n = 0 := by
      ext i; fin_cases i <;> simp <;> omega
    subst hn0
    simpa using h

theorem span_range_eq_of_comp_eq_id {B : Type} [CommRing B] (u v : Series B)
    (hu0 : ∀ i, constantCoeff (u i) = 0) (hv0 : ∀ i, constantCoeff (v i) = 0)
    (hvu : v.comp u = Series.id B) :
    Ideal.span (Set.range u) = Ideal.span (Set.range (Series.id B)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (mem_span_range_id_iff _).mpr (hu0 i)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hX : (Series.id B) i = subst u (v i) := (congrFun hvu i).symm
    rw [hX]
    have hv : v i ∈ Ideal.span (Set.range (Series.id B)) := (mem_span_range_id_iff _).mpr (hv0 i)
    let S : MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2) B := substAlgHom (hasSubst_of_constantCoeff_zero hu0)
    have hS : ∀ g, S g = subst u g := fun g => by
      show substAlgHom (hasSubst_of_constantCoeff_zero hu0) g = subst u g
      rw [coe_substAlgHom]
    have hle : Ideal.map S.toRingHom (Ideal.span (Set.range (Series.id B))) ≤ Ideal.span (Set.range u) := by
      rw [Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      show S.toRingHom (X j) ∈ Ideal.span (Set.range u)
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hS, subst_X (hasSubst_of_constantCoeff_zero hu0)]
      exact Ideal.subset_span ⟨j, rfl⟩
    have := hle (Ideal.mem_map_of_mem _ hv)
    rwa [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hS] at this

theorem hasKernelOfDegree_one_of_comp_eq_id {B : Type} [CommRing B] (u v : Series B)
    (hu0 : ∀ i, constantCoeff (u i) = 0) (hv0 : ∀ i, constantCoeff (v i) = 0)
    (hvu : v.comp u = Series.id B) : FormalODModule.HasKernelOfDegree u 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hid := CerednikDrinfeld.FormalODModule.hasKernelOfDegree_id B
  have key := span_range_eq_of_comp_eq_id u v hu0 hv0 hvu
  have h := CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_span_range_eq 2 u
    (Ideal.span (Set.range (Series.id B))) 0 key hid.1 hid.2.1 (fun κ _ f => by
      have hI : (Ideal.span (Set.range (Series.id B))).map (MvPowerSeries.map f : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) κ)
          = Ideal.span (Set.range (Series.id κ)) := by
        rw [Ideal.map_span]
        congr 1
        ext g
        constructor
        · rintro ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, (MvPowerSeries.map_X f j).symm⟩
        · rintro ⟨j, rfl⟩; exact ⟨X j, ⟨j, rfl⟩, MvPowerSeries.map_X f j⟩
      have h2 := hid.2.2 κ f
      rw [Series.map_id] at h2
      rw [pow_zero, ← h2]
      exact (Ideal.quotientEquivAlgOfEq κ hI).toLinearEquiv.finrank_eq)
  simpa using h

theorem hasHeight_of_isIso {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X Y : FormalODModule p B) (u v : Series B)
    (hu : FormalODModule.IsODHom X Y u) (hv : FormalODModule.IsODHom Y X v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B) {h : ℕ} (hY : Y.HasHeight h) :
    X.HasHeight h := by
  have hu0 : ∀ i, constantCoeff (u i) = 0 := hu.1.1
  have hv0 : ∀ i, constantCoeff (v i) = 0 := hv.1.1
  have hXp : ∀ i, constantCoeff (X.act (p : Zp2 p) i) = 0 := (X.isLawHom_act _).1
  have hYp : ∀ i, constantCoeff (Y.act (p : Zp2 p) i) = 0 := (Y.isLawHom_act _).1
  have e : X.act (p : Zp2 p) = v.comp ((Y.act (p : Zp2 p)).comp u) := by
    rw [← hu.2.1 (p : Zp2 p), ← Series.comp_assoc _ _ _ hu0 hXp, hvu, Series.id_comp _ hXp]
  have hdu : FormalODModule.HasKernelOfDegree u 1 := hasKernelOfDegree_one_of_comp_eq_id u v hu0 hv0 hvu
  have hdv : FormalODModule.HasKernelOfDegree v 1 := hasKernelOfDegree_one_of_comp_eq_id v u hv0 hu0 huv
  have h1 : FormalODModule.HasKernelOfDegree ((Y.act (p : Zp2 p)).comp u) (1 * p ^ h) :=
    CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp hu0 hYp hdu hY
  have h2 : FormalODModule.HasKernelOfDegree (v.comp ((Y.act (p : Zp2 p)).comp u)) (1 * p ^ h * 1) :=
    CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp (Series.constantCoeff_comp hYp hu0) hv0 h1 hdv
  show FormalODModule.HasKernelOfDegree (X.act (p : Zp2 p)) (p ^ h)
  rw [e]; simpa using h2

theorem hasKernelOfDegree_comp_left_of_comp_eq_id {B : Type} [CommRing B] [IsNoetherianRing B]
    (ρ v u : Series B) (hρ0 : ∀ i, constantCoeff (ρ i) = 0)
    (hv0 : ∀ i, constantCoeff (v i) = 0) (hu0 : ∀ i, constantCoeff (u i) = 0)
    (huv : u.comp v = Series.id B) {d : ℕ} (hρ : FormalODModule.HasKernelOfDegree ρ d) :
    FormalODModule.HasKernelOfDegree (v.comp ρ) d := by
  have hdv : FormalODModule.HasKernelOfDegree v 1 := hasKernelOfDegree_one_of_comp_eq_id v u hv0 hu0 huv
  simpa using CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp hρ0 hv0 hρ hdv

theorem isHausdorff_of_isNilpotent {B : Type} [CommRing B] {p : ℕ} (h : IsNilpotent (p : B)) :
    IsHausdorff (Ideal.span {(p : B)}) B := by
  obtain ⟨m, hm⟩ := h
  refine ⟨fun x hx => ?_⟩
  have hx' := SModEq.sub_mem.mp (hx m)
  have hbot : Ideal.span {(p : B)} ^ m = ⊥ := by
    rw [Ideal.span_singleton_pow, hm, Ideal.span_singleton_eq_bot]
  rwa [sub_zero, hbot, Submodule.bot_smul, Submodule.mem_bot] at hx'

end ReduceF1A2

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {L L' : Type} [CommRing L] [CommRing L'] [IsNoetherianRing L] [IsNoetherianRing L']
    (ψ : O →+* L) (ψ' : O →+* L') (hL' : IsNilpotent (p : L'))
    (g : L' →+* L) (hg : g.comp ψ' = ψ) (hgs : Function.Surjective g)
    (hg2 : RingHom.ker g * RingHom.ker g = ⊥)
    (t : Rigidified p Φ L) (ht : t.IsAdmissible ι ψ)
    (γ : Fin 2 → MvFormalGroup.CartierModule p t.X.F) (hγ : t.X.IsHomogeneousVBasis (structureMap ι ψ) γ)
    (a : ℕ → Fin 2 → L) (ha : t.X.HasStructureConstants γ a)
    (α' β' : L') (hα : g α' = a 0 0) (hβ : g β' = a 0 1) (hαβ : α' * β' = (p : L')) :
    ∃ t' : Rigidified p Φ L', t'.IsAdmissible ι ψ' ∧ (t'.map g).IsIsomorphic t := by
  classical

  have hjg : g.comp (structureMap ι ψ') = structureMap ι ψ := by
    show g.comp (ψ'.comp ι) = ψ.comp ι
    rw [← RingHom.comp_assoc, hg]
  have hLnil : IsNilpotent (p : L) := by
    obtain ⟨m, hm⟩ := hL'
    exact ⟨m, by rw [← map_natCast g, ← map_pow, hm, map_zero]⟩
  have hsepL : IsHausdorff (Ideal.span {(p : L)}) L := ReduceF1A2.isHausdorff_of_isNilpotent hLnil
  have hsepL' : IsHausdorff (Ideal.span {(p : L')}) L' := ReduceF1A2.isHausdorff_of_isNilpotent hL'
  have hker : IsNilpotent (RingHom.ker g) := ⟨2, by rw [pow_two]; exact hg2⟩

  choose lift hlift using (fun b : L => hgs b)
  let a' : ℕ → Fin 2 → L' := fun m i => if m = 0 then (if i = 0 then α' else β') else lift (a m i)
  have ha'g : ∀ m i, g (a' m i) = a m i := by
    intro m i
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · fin_cases i
      · simpa [a'] using hα
      · simpa [a'] using hβ
    · simp [a', Nat.pos_iff_ne_zero.mp hm, hlift]
  have hmul' : a' 0 0 * a' 0 1 = (p : L') := by simpa [a'] using hαβ

  obtain ⟨X', γ', hγ', haX'⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq p
      (structureMap ι ψ') a' hmul'

  have hγ'g : (X'.map g).IsHomogeneousVBasis (structureMap ι ψ)
      (fun i => MvFormalGroup.CartierModule.baseChange g (γ' i)) := hjg ▸ hγ'.map g
  have ha'X'g : (X'.map g).HasStructureConstants (fun i => MvFormalGroup.CartierModule.baseChange g (γ' i)) a := by
    have h := haX'.map g
    have e : (fun m i => g (a' m i)) = a := funext fun m => funext fun i => ha'g m i
    rwa [e] at h
  obtain ⟨u, hu, -⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_hasStructureConstants p (structureMap ι ψ) hsepL
      (X'.map g) t.X (fun i => MvFormalGroup.CartierModule.baseChange g (γ' i)) γ hγ'g hγ a ha'X'g ha
  obtain ⟨v, hvu, huv⟩ := hu
  have hvu' : v.toSeries.comp u.toSeries = Series.id L := congrArg FormalODModule.Hom.toSeries hvu
  have huv' : u.toSeries.comp v.toSeries = Series.id L := congrArg FormalODModule.Hom.toSeries huv
  have hu0 : ∀ i, constantCoeff (u.toSeries i) = 0 := u.isODHom.constantCoeff
  have hv0 : ∀ i, constantCoeff (v.toSeries i) = 0 := v.isODHom.constantCoeff

  have hX's : X'.IsSpecial (structureMap ι ψ') :=
    CerednikDrinfeld.FormalODModule.isSpecial_of_isHomogeneousVBasis p (structureMap ι ψ') hsepL' X' γ' hγ'
  have hXgs : (X'.map g).IsSpecial (structureMap ι ψ) :=
    hjg ▸ CerednikDrinfeld.FormalODModule.IsSpecial.map (structureMap ι ψ') g X' hX's
  have hXg4 : (X'.map g).HasHeight 4 :=
    ReduceF1A2.hasHeight_of_isIso (X'.map g) t.X u.toSeries v.toSeries u.isODHom v.isODHom hvu' huv' ht.2.1
  have hX'4 : X'.HasHeight 4 := by
    have h4 : FormalODModule.HasKernelOfDegree ((X'.act (p : Zp2 p)).map g) (p ^ 4) := by
      rw [← FormalODModule.map_act]; exact hXg4
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_map_of_surjective_of_isNilpotent_ker g hgs hker
      (X'.act (p : Zp2 p)) (X'.isLawHom_act _).1 (pow_pos (Fact.out : p.Prime).pos 4) h4

  let mk : L →+* L ⧸ pIdeal p L := Ideal.Quotient.mk (pIdeal p L)
  let ts : Rigidified p Φ L := ⟨X'.map g, t.n, (v.toSeries.map mk).comp t.ρ⟩
  have hρ0 : ∀ i, constantCoeff (t.ρ i) = 0 := ht.constantCoeff_ρ
  have hvb : FormalODModule.IsODHom t.Xbar ts.Xbar (v.toSeries.map mk) := v.isODHom.map mk
  have hub : FormalODModule.IsODHom ts.Xbar t.Xbar (u.toSeries.map mk) := u.isODHom.map mk
  have hubvb : (u.toSeries.map mk).comp (v.toSeries.map mk) = Series.id (L ⧸ pIdeal p L) := by
    rw [← Series.map_comp _ _ _ hv0, huv', Series.map_id]
  have hts : ts.IsAdmissible ι ψ := by
    refine ⟨hXgs, hXg4, ?_, ?_⟩
    · exact hvb.comp ht.2.2.1
    · exact ReduceF1A2.hasKernelOfDegree_comp_left_of_comp_eq_id t.ρ (v.toSeries.map mk) (u.toSeries.map mk)
        hρ0 hvb.constantCoeff hub.constantCoeff hubvb ht.2.2.2

  obtain ⟨n', ρ', hadm', m, hm⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_mk_and_act_pow_comp_map_eq_of_map_eq_of_surjective_of_isNilpotent
      ι Φ g hgs hker hL' ψ' ψ hg X' hX's hX'4 ts hts rfl
  refine ⟨⟨X', n', ρ'⟩, hadm', ?_⟩

  refine ⟨u.toSeries, v.toSeries, m, u.isODHom, v.isODHom, hvu', huv', ?_⟩
  have hρ'0 : ∀ i, constantCoeff ((ρ'.map (reduceMap g)) i) = 0 := fun i => by
    show constantCoeff (MvPowerSeries.map (reduceMap g) (ρ' i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hadm'.constantCoeff_ρ i, map_zero]
  have hact0 : ∀ (Y : FormalODModule p (L ⧸ pIdeal p L)) (c : Zp2 p) (i : Fin 2), constantCoeff (Y.act c i) = 0 :=
    fun Y c => (Y.isLawHom_act c).1
  have key := congrArg (fun s => (u.toSeries.map mk).comp s) hm

  have lhs : (u.toSeries.map mk).comp ((ts.Xbar.act ((p : Zp2 p) ^ (m + ts.n))).comp (ρ'.map (reduceMap g))) =
      (t.Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp ((u.toSeries.map mk).comp (ρ'.map (reduceMap g))) := by
    rw [← Series.comp_assoc _ _ _ (hact0 _ _) hρ'0, hub.2.1, Series.comp_assoc _ _ _ hub.constantCoeff hρ'0]
  have rhs : (u.toSeries.map mk).comp ((ts.Xbar.act ((p : Zp2 p) ^ (m + n'))).comp ts.ρ) =
      (t.Xbar.act ((p : Zp2 p) ^ (m + n'))).comp t.ρ := by
    have hvρ0 : ∀ i, constantCoeff (ts.ρ i) = 0 := fun i =>
      Series.constantCoeff_comp hvb.constantCoeff hρ0 i
    rw [← Series.comp_assoc _ _ _ (hact0 _ _) hvρ0, hub.2.1, Series.comp_assoc _ _ _ hub.constantCoeff hvρ0]
    show (t.Xbar.act ((p : Zp2 p) ^ (m + n'))).comp ((u.toSeries.map mk).comp ((v.toSeries.map mk).comp t.ρ)) = _
    rw [← Series.comp_assoc _ _ _ hvb.constantCoeff hρ0, hubvb, Series.id_comp _ hρ0]
  rw [lhs, rhs] at key
  exact key

#print axioms solution

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_of_hasStructureConstants_of_map_eq_of_mul_eq_of_ker_mul_ker_eq_bot
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_of_hasStructureConstants_of_map_eq_of_mul_eq_of_ker_mul_ker_eq_bot (solution)
