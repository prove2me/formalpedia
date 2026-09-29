-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_map_nMap_of_isBaseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/95e1d519-fe2d-5a0d-b6ea-ba75f0eac83c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_map_nMap_of_isBaseChangeAlong

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace K77COL3
namespace EtaBC

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] {j : CerednikDrinfeld.Zp2 p →+* B}
  {j' : CerednikDrinfeld.Zp2 p →+* B'}
  (D : CerednikDrinfeld.GradedCartierModuleData p B j) (D' : CerednikDrinfeld.GradedCartierModuleData p B' j')
  (bc : D.M →+ D'.M)
  (hV : ∀ x, bc (D.verschiebung x) = D'.verschiebung (bc x)) (hPi : ∀ x, bc (D.varpi x) = D'.varpi (bc x))

theorem phi_nMap (L : D.M →+ D.NMod) (hLV : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hLV' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ x, L' (bc x) = D.nMap D' bc hV hPi (L x)) (z : D.NMod) :
    D'.phi L' hLV' (D.nMap D' bc hV hPi z) = D.nMap D' bc hV hPi (D.phi L hLV z) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
  rw [nMap_nMk, phi_nMk, phi_nMk, map_add, hLL', nMap_nMk, map_zero]

theorem nMap_mem_eta (L : D.M →+ D.NMod) (hLV : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hLV' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ x, L' (bc x) = D.nMap D' bc hV hPi (L x)) (z : D.NMod) (hz : z ∈ D.eta L hLV) :
    D.nMap D' bc hV hPi z ∈ D'.eta L' hLV' := by
  rw [mem_eta_iff] at hz ⊢
  rw [phi_nMap D D' bc hV hPi L hLV L' hLV' hLL', hz]

theorem nMap_mem_nPiece (hpiece : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → bc x ∈ D'.piece i) (i : Fin 2)
    (z : D.NMod) (hz : z ∈ D.nPiece i) : D.nMap D' bc hV hPi z ∈ D'.nPiece i := by
  unfold nPiece at hz ⊢
  rw [AddSubgroup.mem_map] at hz ⊢
  obtain ⟨⟨x, x'⟩, hx, rfl⟩ := hz
  rw [AddSubgroup.mem_prod] at hx
  refine ⟨(bc x, bc x'), ?_, ?_⟩
  · rw [AddSubgroup.mem_prod]
    exact ⟨hpiece i x hx.1, hpiece i x' hx.2⟩
  · rw [nMap_nMk]

theorem nMap_nVarpi (z : D.NMod) : D.nMap D' bc hV hPi (D.nVarpi z) = D'.nVarpi (D.nMap D' bc hV hPi z) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
  have h1 : D.nVarpi (D.nMk (x, x')) = D.nMk (D.varpi x, D.varpi x') := rfl
  have h2 : D'.nVarpi (D'.nMk (bc x, bc x')) = D'.nMk (D'.varpi (bc x), D'.varpi (bc x')) := rfl
  rw [h1, nMap_nMk, nMap_nMk, h2, hPi, hPi]

theorem nMap_nVarpi_pow (k : ℕ) (z : D.NMod) :
    D.nMap D' bc hV hPi (((D.nVarpi : D.NMod →ₗ[WittVector p B] D.NMod) ^ k) z) =
      ((D'.nVarpi : D'.NMod →ₗ[WittVector p B'] D'.NMod) ^ k) (D.nMap D' bc hV hPi z) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, nMap_nVarpi]

end K77COL3.EtaBC

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ')
    (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hOD' : FormalODModule.IsODHom ((t.map f).Φbar ψ') (t.map f).Xbar (t.map f).ρ)
    {S S' : Type} [CommRing S] [CommRing S'] (g : B →+* S) (g' : B' →+* S') (e : S →+* S')
    (hge : g'.comp f = e.comp g)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (hc' : (t.map f).IsGradedS ι ψ' g') (hcb' : (t.map f).IsGradedSbar ι ψ' g')
    (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' g')
    (bc : MvFormalGroup.CartierModule p (t.XS g).F →+ MvFormalGroup.CartierModule p ((t.map f).XS g').F)
    (hbc : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' e ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (L' : (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').M →+ (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').NMod) (hL' : (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').IsCanonicalLMap L')
    (hLL' : ∀ x, L' (bc x) = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 (L x))
    (bcbar : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod →+ (((t.map (f : B →+* B')).XbarS g').toGradedCartierModuleData (Rigidified.jSbar ι ψ' g') hcb').NMod)
    (hred : ∀ z, (t.map f).etaRed ι ψ' g' hc' hcb' (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 z) =
      bcbar (t.etaRed ι ψ g hc hcb z))
    (hrig : ∀ w, (t.map f).rigidNum ι hcΦ rΦ ψ' hOD' g' hcb' hcΦg' w = bcbar (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg w))
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v) :
    (t.map f).IsEtaSection ι hcΦ rΦ ψ' hOD' g' hc' hcb' hcΦg' L' hL' i
      (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 z) v := by
  obtain ⟨hz1, hz2⟩ := hz
  have hη := K77COL3.EtaBC.nMap_mem_eta ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 L hL.isCartierLMap.map_verschiebung
    L' hL'.isCartierLMap.map_verschiebung hLL' z (AddSubgroup.mem_inf.mp hz1).1
  have hπ := K77COL3.EtaBC.nMap_mem_nPiece ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 hbc.2.2.2.2.1 i z (AddSubgroup.mem_inf.mp hz1).2
  have hcomm := K77COL3.EtaBC.nMap_nVarpi_pow ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 (i : ℕ) z
  refine ⟨AddSubgroup.mem_inf.mpr ⟨hη, hπ⟩, ?_⟩
  obtain ⟨m, k, w, hw1, hw2⟩ := hz2
  refine ⟨m, k, w, hw1, ?_⟩
  rw [Rigidified.map_n, hrig, ← hcomm, hred, ← map_nsmul bcbar, ← map_nsmul bcbar, hw2]

end S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_map_nMap_of_isBaseChangeAlong
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_map_nMap_of_isBaseChangeAlong (solution)
