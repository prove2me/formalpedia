-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.homPreservesCochains_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:16.024237+00:00
-- url     : https://prove2.me/submissions/ceae7fbc-b1e7-40e0-b899-93f1c2c21f41

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_LenBound
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.CoboundaryTransfers
section SlopeTestRemainingChoices
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
private theorem WachMod.mem_cocycles_units_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := by
  simp [WachMod.Z1, WachMod.d1, sub_eq_add_neg]
private theorem WachMod.WachMod_mem_B1_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.B1 ↔ ∃ x, (W.φ x - x, W.γ x - x) = pr := by
  simp [WachMod.B1]
end SlopeTestRemainingChoices
end Formalism.CoboundaryTransfers
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : HomMaps := by
  intro O A _ _ _ B M D D' _ _ _ _ _ _ _ _ W W' F
  have hQ : ∀ y, W.QInv y → W'.QInv (F.f y) := fun y hy => by
    show B.Q ^ M • F.f y ∈ W'.N
    rw [← map_smul]
    exact F.N_le _ hy
  have hX : ∀ z, W.XN z → W'.XN (F.f z) := by
    rintro z ⟨n, hn, rfl⟩
    exact ⟨F.f n, F.N_le n hn, map_smul _ _ _⟩
  have hC1 : ∀ y z, W.C1 y z → W'.C1 (F.f y) (F.f z) := fun y z h => ⟨hQ y h.1, hX z h.2⟩
  have hd : ∀ y z, F.f (W.d1 y z) = W'.d1 (F.f y) (F.f z) := fun y z => by
    simp only [WachMod.d1, map_sub, F.φ_comm, F.γ_comm]
  have hZ1 : W.Z1.map F.f2 ≤ W'.Z1 := by
    rintro _ ⟨pr, hpr, rfl⟩
    refine (WachMod.mem_cocycles_units_iff W' _).mpr ?_
    show W'.d1 (F.f pr.1) (F.f pr.2) = 0
    rw [← hd, (WachMod.mem_cocycles_units_iff W pr).mp hpr, map_zero]
  have hB1 : W.B1.map F.f2 ≤ W'.B1 := by
    rintro _ ⟨pr, hpr, rfl⟩
    obtain ⟨x, rfl⟩ := (WachMod.WachMod_mem_B1_iff W pr).mp hpr
    exact (WachMod.WachMod_mem_B1_iff W' _).mpr ⟨F.f x, by simp [Hom.f2, F.φ_comm, F.γ_comm]⟩
  have hZf : W.Zf.map F.f2 ≤ W'.Zf := by
    refine Submodule.map_le_iff_le_comap.mpr ?_
    rw [WachMod.Zf]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro pr ⟨hz, a, b, hb, hint⟩
      refine Submodule.mem_comap.mpr ?_
      rw [WachMod.Zf]
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨hZ1 ⟨pr, hz, rfl⟩, a, F.f2 b, hB1 ⟨b, hb, rfl⟩, ?_⟩
      obtain ⟨⟨k, hk⟩, hxn⟩ := hint
      have e : (B.p ^ a : ℕ) • F.f2 pr + F.f2 b = F.f2 ((B.p ^ a : ℕ) • pr + b) := by
        rw [map_add, map_nsmul]
      rw [e]
      refine ⟨⟨k, ?_⟩, hX _ hxn⟩
      show B.Q ^ k • F.f (((B.p ^ a : ℕ) • pr + b).1) ∈ W'.N
      rw [← map_smul]
      exact F.N_le _ hk
    · intro pr hpr
      refine Submodule.mem_comap.mpr ?_
      rw [WachMod.Zf]
      exact Submodule.mem_sup_right (hB1 ⟨pr, hpr, rfl⟩)
  refine ⟨hQ, hX, ?_, hd, ?_, ?_, ?_, hZ1, hB1, hZf⟩
  · rintro ω ⟨y, hy, rfl⟩
    exact ⟨F.f y, hQ y hy, map_smul _ _ _⟩
  · rintro y z ⟨h1, h2⟩
    exact ⟨hC1 y z h1, by rw [← hd, h2, map_zero]⟩
  · rintro y z ⟨x, hx, rfl, rfl⟩
    exact ⟨F.f x, F.N_le x hx, by rw [map_sub, F.φ_comm], by rw [map_sub, F.γ_comm]⟩
  · rintro ω ⟨y, z, h, rfl⟩
    exact ⟨F.f y, F.f z, hC1 y z h, hd y z⟩
end Formalism.CoboundaryTransfers
