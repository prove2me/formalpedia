-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.stalkMap_inclBaseChange_eq_map_of_tangent_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/261de0ed-4eb1-53e7-9840-75aa13d205a7

import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_map_varpi
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_inclBaseChange_eq_map_of_tangent_germ

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace StalkPi

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

section Datum

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

theorem nVarpi_nMk (D : GradedCartierModuleData p B j) (m m' : D.M) :
    D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem nsmul_nMk (D : GradedCartierModuleData p B j) (k : ℕ) (m m' : D.M) :
    k • D.nMk (m, m') = D.nMk (k • m, k • m') := by
  rw [← map_nsmul]; rfl

theorem nVarpi_nVarpi (D : GradedCartierModuleData p B j) (z : D.NMod) :
    D.nVarpi (D.nVarpi z) = (p : ℕ) • z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nVarpi_nMk, D.varpi_varpi, D.varpi_varpi, nsmul_nMk]

theorem toLieQuot_nMk (D : GradedCartierModuleData p B j) (m m' : D.M) :
    D.toLieQuot (D.nMk (m, m')) = D.vRange.mkQ m := rfl

theorem nVarpi_mem_etaPiece (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (i : Fin 2) (z : D.NMod)
    (hz : z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i) :
    D.nVarpi z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung (i + 1) := by
  obtain ⟨hfix, hpiece⟩ := AddSubgroup.mem_inf.mp hz
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hpiece
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_eta_iff] at hfix ⊢
    rw [nVarpi_nMk, phi_nMk,
      CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.map_varpi p j D hD L hL a]
    have h0 : D.nMk (D.varpi b, 0) = D.nVarpi (D.nMk (b, 0)) := by rw [nVarpi_nMk, map_zero]
    rw [h0, ← map_add, ← phi_nMk D L hL.isCartierLMap.map_verschiebung a b, hfix, nVarpi_nMk]
  · rw [nVarpi_nMk]
    exact AddSubgroup.mem_map.mpr ⟨(D.varpi a, D.varpi b),
      AddSubgroup.mem_prod.mpr ⟨D.varpi_mem i a ha, D.varpi_mem i b hb⟩, rfl⟩

theorem mkQ_varpi_eq_toLieQuot_nVarpi (D : GradedCartierModuleData p B j) (z : D.NMod) (m : D.M)
    (hm : D.vRange.mkQ m = D.toLieQuot z) :
    D.vRange.mkQ (D.varpi m) = D.toLieQuot (D.nVarpi z) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [toLieQuot_nMk] at hm
  rw [nVarpi_nMk, toLieQuot_nMk]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hm ⊢
  obtain ⟨y, hy⟩ := (D.mem_vRange_iff _).mp hm
  exact (D.mem_vRange_iff _).mpr ⟨D.varpi y, by rw [← D.varpi_verschiebung, hy, map_sub]⟩

theorem latticeRel_nsmul (D : GradedCartierModuleData p B j) {n : ℕ} {r : (Fin 2 → ℤ_[p]) →+ D.NMod}
    {zbar : D.NMod} {v : Fin 2 → ℚ_[p]} (h : Rigidified.LatticeRel D n r zbar v) :
    Rigidified.LatticeRel D n r ((p : ℕ) • zbar) ((p : ℚ_[p]) • v) := by
  obtain ⟨m, k, w, hw, hrel⟩ := h
  refine ⟨m, k, (p : ℕ) • w, ?_, ?_⟩
  · rw [smul_comm, hw]
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, PadicInt.coe_mul, PadicInt.coe_natCast]
    rfl
  · rw [map_nsmul, smul_comm (p ^ k), hrel]
    exact smul_comm _ _ _

end Datum

section Tangent

variable {p : ℕ} [Fact p.Prime]

theorem tangent_eq_of_mkQ_eq {S : Type} [CommRing S] (X : FormalODModule p S) (jS : Zp2 p →+* S)
    (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1)) (m m' : CartierModule p X.F)
    (h : (X.toGradedCartierModuleData jS hc).vRange.mkQ m = (X.toGradedCartierModuleData jS hc).vRange.mkQ m') :
    tangent m = tangent m' := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨y, hy⟩ := ((X.toGradedCartierModuleData jS hc).mem_vRange_iff _).mp h
  have hy' : verschiebungInt y = m - m' := hy
  have : tangent (m - m') = 0 := by
    rw [← hy']
    exact tangent_verschiebungInt y
  rwa [map_sub, sub_eq_zero] at this

theorem tangent_varpi {B S : Type} [CommRing B] [CommRing S] (X : FormalODModule p B) (g : B →+* S)
    (m : CartierModule p (X.map g).F) :
    tangent (endAct (X.map g).varpiEnd m) = ((linearPart X.varpi).map g).mulVec (tangent m) := by
  have hL : linearPart (X.map g).varpiEnd.toPowerSeries = (linearPart X.varpi).map g := by
    ext i k
    simp only [linearPart, Matrix.of_apply, Matrix.map_apply]
    exact MvPowerSeries.coeff_map _ _ _
  rw [endAct_apply, tangent_map, hL]

end Tangent

section Loc

theorem mk_eq_map_mk {B : Type} [CommRing B] (x : PrimeSpectrum B) (f : B) (hf : f ∉ x.asIdeal)
    (P Q : Submodule B (Fin 2 → B)) (Pi : ↥P →ₗ[B] ↥Q) (A : Matrix (Fin 2) (Fin 2) B)
    (hPi : ∀ s : ↥P, ((Pi s : ↥Q) : Fin 2 → B) = A.mulVec (s : Fin 2 → B))
    (s : ↥P) (b : x.asIdeal.primeCompl) (τ : Fin 2 → Rigidified.Baway f)
    (hs : ∀ i, Rigidified.locHom x ((s : Fin 2 → B) i) = Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (τ i))
    (s' : ↥Q) (b' : x.asIdeal.primeCompl)
    (hs' : ∀ i, Rigidified.locHom x ((s' : Fin 2 → B) i) =
      Rigidified.locHom x (b' : B) * Rigidified.awayToLoc x f hf ((A.map (Rigidified.awayHom f)).mulVec τ i)) :
    LocalizedModule.mk s' b' = LocalizedModule.map x.asIdeal.primeCompl Pi (LocalizedModule.mk s b) := by
  rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]

  have key : ∀ i, Rigidified.locHom x ((b : B) * (s' : Fin 2 → B) i) =
      Rigidified.locHom x ((b' : B) * ((Pi s : ↥Q) : Fin 2 → B) i) := by
    intro i
    have hA : Rigidified.locHom x (A.mulVec (s : Fin 2 → B) i) =
        Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf ((A.map (Rigidified.awayHom f)).mulVec τ i) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : Rigidified.awayToLoc x f hf (Rigidified.awayHom f (A i k)) = Rigidified.locHom x (A i k) := by
        unfold Rigidified.awayToLoc
        exact IsLocalization.Away.lift_eq f _ (A i k)
      rw [hk]; ring
    rw [map_mul, map_mul, hs', hPi, hA]; ring
  have key' : ∀ i, ∃ c : x.asIdeal.primeCompl,
      (c : B) * ((b : B) * (s' : Fin 2 → B) i) = (c : B) * ((b' : B) * ((Pi s : ↥Q) : Fin 2 → B) i) :=
    fun i => (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal)).mp (key i)
  obtain ⟨c₀, hc₀⟩ := key' 0
  obtain ⟨c₁, hc₁⟩ := key' 1
  refine ⟨c₀ * c₁, ?_⟩
  apply Subtype.ext
  funext i
  change ((c₀ : B) * c₁) * ((b : B) * (s' : Fin 2 → B) i) =
    ((c₀ : B) * c₁) * ((b' : B) * ((Pi s : ↥Q) : Fin 2 → B) i)
  fin_cases i
  · simp only [Fin.zero_eta]
    linear_combination (c₁ : B) * hc₀
  · simp only [Fin.mk_one]
    linear_combination (c₀ : B) * hc₁

end Loc

end StalkPi

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
    (hfull₀ : ∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) (hfull₁ : ∀ x, LT.LatticeTree.IsFullLattice (N₁ x))
    (hle : ∀ x, N₀ x ≤ N₁ x) (hsmul : ∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x)
    (Pi₀ : ↥(t.X.lieZero (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) (Pi₁ : ↥(t.X.lieOne (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (hPi₀ : ∀ s : ↥(t.X.lieZero (structureMap ι ψ)), ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
    (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))
    (hg₀ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieZero (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
    (hg₁ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieOne (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i))) :
    (∀ x w, u₁ x (FormalOmega.inclBaseChange (FormalOmega.locRing B x) (M' := ⟨N₀ x, hfull₀ x⟩) (M := ⟨N₁ x, hfull₁ x⟩) (hle x) w) =
          LocalizedModule.map x.asIdeal.primeCompl Pi₀ (u₀ x w)) ∧
      (∀ x w, u₀ x (((FormalOmega.smulInto (p : ℤ_[p]) (hsmul x)).baseChange (FormalOmega.locRing B x) :
            FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
              FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩) w) =
          LocalizedModule.map x.asIdeal.primeCompl Pi₁ (u₁ x w)) := by

  have hDsp : ∀ (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
      (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L), ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsSpecialCartierModule := by
    intro f hc L hL
    obtain ⟨S', _, jS', φ, _, _, Dl, _, f', hf', Ll, _, _⟩ := hL.exists_lift
    obtain ⟨γ, _, hγ'⟩ := hf'.2.2.2.2.2
    exact ⟨⟨fun i => f' (γ i), hγ'⟩, fun x =>
      MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
        p (t.XS (Rigidified.awayHom f)).F x⟩
  have hA : ∀ (s : ↥(t.X.lieZero (structureMap ι ψ))),
      ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = (MvFormalGroup.linearPart t.X.varpi).mulVec (s : t.X.Lie) :=
    fun s => by rw [hPi₀]; rfl
  have hA' : ∀ (s : ↥(t.X.lieOne (structureMap ι ψ))),
      ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = (MvFormalGroup.linearPart t.X.varpi).mulVec (s : t.X.Lie) :=
    fun s => by rw [hPi₁]; rfl

  have gen₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x),
      u₁ x (FormalOmega.inclBaseChange (FormalOmega.locRing B x) (M' := ⟨N₀ x, hfull₀ x⟩) (M := ⟨N₁ x, hfull₁ x⟩) (hle x)
        ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x)))) =
      LocalizedModule.map x.asIdeal.primeCompl Pi₀ (u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x)))) := by
    intro x v hv
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz0⟩ := (hN₀ x v).mp hv
    have hD := hDsp f hc L hL
    have hz0' := hz0
    rw [Rigidified.isEtaSection_zero_iff] at hz0'
    have hz1 : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nVarpi z) v := by
      rw [Rigidified.isEtaSection_one_iff]
      refine ⟨StalkPi.nVarpi_mem_etaPiece _ hD L hL 0 z hz0'.1, ?_⟩
      rw [StalkPi.nVarpi_nVarpi, map_nsmul]
      exact StalkPi.latticeRel_nsmul _ hz0'.2
    obtain ⟨m, s, b, hm, hu0, hs⟩ := hg₀ x v hv f hf hc hcb hcΦf L hL z hz0
    obtain ⟨m', s', b', hm', hu1, hs'⟩ := hg₁ x v (hle x hv) f hf hc hcb hcΦf L hL _ hz1
    have hincl : FormalOmega.inclBaseChange (FormalOmega.locRing B x) (M' := ⟨N₀ x, hfull₀ x⟩) (M := ⟨N₁ x, hfull₁ x⟩) (hle x)
        ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) =
        (1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hle x hv⟩ : ↥(N₁ x)) := by
      unfold FormalOmega.inclBaseChange
      rw [LinearMap.baseChange_tmul]
      rfl
    rw [hincl, hu1, hu0]
    have htan : MvFormalGroup.CartierModule.tangent m' =
        ((MvFormalGroup.linearPart t.X.varpi).map (Rigidified.awayHom f)).mulVec (MvFormalGroup.CartierModule.tangent m) := by
      rw [← StalkPi.tangent_varpi]
      apply StalkPi.tangent_eq_of_mkQ_eq (t.XS (Rigidified.awayHom f)) (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc
      rw [hm']
      exact (StalkPi.mkQ_varpi_eq_toLieQuot_nVarpi _ z m hm).symm
    exact StalkPi.mk_eq_map_mk x f hf _ _ Pi₀ _ hA s b _ hs s' b' (fun i => by rw [← htan]; exact hs' i)

  have gen₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x),
      u₀ x (((FormalOmega.smulInto (p : ℤ_[p]) (hsmul x)).baseChange (FormalOmega.locRing B x) :
            FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
              FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩)
        ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x)))) =
      LocalizedModule.map x.asIdeal.primeCompl Pi₁ (u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x)))) := by
    intro x v hv
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz1⟩ := (hN₁ x v).mp hv
    have hD := hDsp f hc L hL
    have hz1' := hz1
    rw [Rigidified.isEtaSection_one_iff] at hz1'
    have hpv : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v = (p : ℚ_[p]) • v := by rw [map_natCast]
    have hz0 : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nVarpi z)
        (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v) := by
      rw [Rigidified.isEtaSection_zero_iff, hpv]
      exact ⟨StalkPi.nVarpi_mem_etaPiece _ hD L hL 1 z hz1'.1, hz1'.2⟩
    obtain ⟨m, s, b, hm, hu1, hs⟩ := hg₁ x v hv f hf hc hcb hcΦf L hL z hz1
    obtain ⟨m', s', b', hm', hu0, hs'⟩ := hg₀ x _ (hsmul x v hv) f hf hc hcb hcΦf L hL _ hz0
    have hsm : ((FormalOmega.smulInto (p : ℤ_[p]) (hsmul x)).baseChange (FormalOmega.locRing B x) :
            FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
              FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩)
          ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) =
        (1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v, hsmul x v hv⟩ : ↥(N₀ x)) := by
      rw [LinearMap.baseChange_tmul]
      rfl
    rw [hsm, hu0, hu1]
    have htan : MvFormalGroup.CartierModule.tangent m' =
        ((MvFormalGroup.linearPart t.X.varpi).map (Rigidified.awayHom f)).mulVec (MvFormalGroup.CartierModule.tangent m) := by
      rw [← StalkPi.tangent_varpi]
      apply StalkPi.tangent_eq_of_mkQ_eq (t.XS (Rigidified.awayHom f)) (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc
      rw [hm']
      exact (StalkPi.mkQ_varpi_eq_toLieQuot_nVarpi _ z m hm).symm
    exact StalkPi.mk_eq_map_mk x f hf _ _ Pi₁ _ hA' s b _ hs s' b' (fun i => by rw [← htan]; exact hs' i)
  refine ⟨fun x w => ?_, fun x w => ?_⟩
  · induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul c vv =>
      obtain ⟨v, hv⟩ := vv
      have htm : c ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x)) =
          c • ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [htm, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, gen₀ x v hv]
  · induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul c vv =>
      obtain ⟨v, hv⟩ := vv
      have htm : c ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x)) =
          c • ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [htm, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, gen₁ x v hv]

end S_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_inclBaseChange_eq_map_of_tangent_germ
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_inclBaseChange_eq_map_of_tangent_germ (solution)
