-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_germ_dual_and_transport_and_hasKernelOfDegree_of_isIsogenyPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c87ec206-8112-5c5d-8cda-a520f11ad1c7

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Theorems.Thm_Subring_mem_centralizer_of_mul_eq_of_mul_eq_of_forall_mul_eq_mul
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_of_natCast_pow_mul_eq_of_hasHeight
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight
import Theorems.Thm_CerednikDrinfeld_isAlgClosed_and_charP_quotient_of_isMaximal_of_forall_monic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_germ_dual_and_transport_and_hasKernelOfDegree_of_isIsogenyPair
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem solution
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (K₀ : Type) [Field K₀] [CharZero K₀]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ β₀' : Series (Onr ⧸ pIdeal r Onr)) (N₀ : ℕ)
    (E₀ : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀) (hE₀ : Function.Injective E₀)
    (E_X : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hAd : ∀ ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
      ∃ e : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})),
        (e : MvFormalGroup.End Φ.F).toPowerSeries =
          β₀'.comp ((Series.map κ (ε : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
        E₀ e = ((r : K₀) ^ N₀) • E_X ε)

    (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (d : ℕ) (hff' : FakeEllipticCurve.IsIsogenyPair (r ^ d) A₀ A₀ f f')
    (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})))
    (hε : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) = mapPt f hf (θ₀ B' s)) :
    ∃ (hf' : f' ≫ A₀.f = A₀.f) (ε' : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})))
      (e e' : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) (m' : ℕ),
      (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
        J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε' : MvFormalGroup.End X₀.F).toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s)) ∧
      ε * ε' = ((r ^ d : ℕ) : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) ∧
      ε' * ε = ((r ^ d : ℕ) : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) ∧
      (e : MvFormalGroup.End Φ.F).toPowerSeries =
        β₀'.comp ((Series.map κ (ε : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
      (e' : MvFormalGroup.End Φ.F).toPowerSeries =
        β₀'.comp ((Series.map κ (ε' : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
      E₀ e = ((r : K₀) ^ N₀) • E_X ε ∧ E₀ e' = ((r : K₀) ^ N₀) • E_X ε' ∧
      e * e' = ((r ^ (2 * N₀ + d) : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) ∧
      FormalODModule.HasKernelOfDegree ((e' : MvFormalGroup.End Φ.F).toPowerSeries) (r ^ (2 * m')) := by
  classical
  have hf' : f' ≫ A₀.f = A₀.f := by
    obtain ⟨_, h, _⟩ := hff'
    exact h
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hdΛ : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ (r ^ d)

  obtain ⟨ε', hε', hmul⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair A₀ coord X₀ θ₀ hA₀ d hdΛ f f' hff' hf hf' (ε : MvFormalGroup.End X₀.F) hε
  have hδ := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia A₀ coord hcoord X₀ θ₀ hA₀ h1Λ (r ^ d) hdΛ
  obtain ⟨hε'ε, hεε'⟩ := hmul ((r ^ d : ℕ) : MvFormalGroup.End X₀.F)
    (fun B' _ _ J m hJ s hs => hδ B' J m hJ s hs)

  haveI hmaxπ : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal := hOnr_max
  letI : Field (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) := Ideal.Quotient.field _

  have hε'mem : ε' ∈ Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}) :=
    Subring.mem_centralizer_of_mul_eq_of_mul_eq_of_forall_mul_eq_mul _ (ε : MvFormalGroup.End X₀.F) ε' _ ε.2 hεε' hε'ε
      (fun x => Nat.cast_commute _ x) (fun x y hxy => CerednikDrinfeld.FormalODModule.eq_of_natCast_pow_mul_eq_of_hasHeight X₀ hX₀ d x y hxy)

  obtain ⟨e, he, hE₀e⟩ := hAd ε
  obtain ⟨e', he', hE₀e'⟩ := hAd ⟨ε', hε'mem⟩
  have hprod : ε * ⟨ε', hε'mem⟩ = ((r ^ d : ℕ) : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :=
    Subtype.ext (by push_cast; exact_mod_cast hεε')
  have hprod' : ⟨ε', hε'mem⟩ * ε = ((r ^ d : ℕ) : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) :=
    Subtype.ext (by push_cast; exact_mod_cast hε'ε)

  have hee' : e * e' = ((r ^ (2 * N₀ + d) : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) := by
    apply hE₀
    rw [map_mul, hE₀e, hE₀e', smul_mul_smul_comm, ← map_mul, hprod, map_natCast, map_natCast]
    rw [← map_natCast (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)), ← map_natCast (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)),
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 1
    push_cast
    ring

  have hpr : pIdeal r Onr = Ideal.span {algebraMap 𝒪 Onr π} := by
    have h1 : Ideal.map (algebraMap 𝒪 Onr) (Ideal.span {((r : ℕ) : 𝒪)}) = Ideal.map (algebraMap 𝒪 Onr) (Ideal.span {π}) := by
      rw [hunr]
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast] at h1
    exact h1
  haveI hmaxr : (pIdeal r Onr).IsMaximal := by rw [hpr]; exact hOnr_max
  letI instF : Field (Onr ⧸ pIdeal r Onr) := Ideal.Quotient.field (pIdeal r Onr)
  obtain ⟨hac, hcp⟩ := CerednikDrinfeld.isAlgClosed_and_charP_quotient_of_isMaximal_of_forall_monic 𝒪 π hunr Onr hOnr_max hOnr_closed
  have hbridge : ∀ (I : Ideal Onr) (hI : I.IsMaximal), I = Ideal.span {algebraMap 𝒪 Onr π} →
      @IsAlgClosed (Onr ⧸ I) (@Ideal.Quotient.field Onr _ I hI) ∧ CharP (Onr ⧸ I) r := by
    rintro I hI rfl
    exact ⟨hac, hcp⟩
  obtain ⟨hacr, hcpr⟩ := hbridge (pIdeal r Onr) hmaxr hpr
  haveI : IsAlgClosed (Onr ⧸ pIdeal r Onr) := hacr
  haveI : CharP (Onr ⧸ pIdeal r Onr) r := hcpr
  obtain ⟨m', hm'⟩ := CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight r ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι) Φ hΦ hΦ4 e e' (2 * N₀ + d) hee'
  exact ⟨hf', ⟨ε', hε'mem⟩, e, e', m', hε', hprod, hprod', he, he', hE₀e, hE₀e', hee', hm'⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_germ_dual_and_transport_and_hasKernelOfDegree_of_isIsogenyPair
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_germ_dual_and_transport_and_hasKernelOfDegree_of_isIsogenyPair (solution)
