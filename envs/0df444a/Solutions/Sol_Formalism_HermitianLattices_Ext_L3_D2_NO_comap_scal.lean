-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.comap_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:58.696326+00:00
-- url     : https://prove2.me/submissions/f2632cba-6c96-410d-a539-234af21ca5bf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_scal_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution {κ : Type} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (hπ0 : algebraMap F K (π : F) ≠ 0) (k c : ℕ) (f g d : κ → κ → K)
    (hf : ∀ i j, f i j ≠ 0)
    (hd : ∀ i j, f i j * d i j = g i j * algebraMap F K (π : F) ^ c) :
    (matL 𝔭 (k + c) f g).comap (scal κ 𝔭 (algebraMap F K (π : F) ^ k)) =
      AddSubgroup.pi Set.univ
        (fun p : κ × κ => (zR 𝔭 (d p.1 p.2)).addSubgroupOf (pK K 𝔭 0).toAddSubgroup) := by
  ext v
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  constructor
  · rintro hv ⟨i, j⟩ -
    obtain ⟨w, hw, e⟩ := hv i j
    obtain ⟨b, hb, rfl⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 hw
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨b, hb, ?_⟩
    show d i j * b = (v (i, j) : K)
    rw [scal_apply] at e
    apply mul_left_cancel₀ (mul_ne_zero (hf i j) (pow_ne_zero k hπ0))
    calc f i j * algebraMap F K (π : F) ^ k * (d i j * b)
        = (f i j * d i j) * (algebraMap F K (π : F) ^ k * b) := by ring
      _ = g i j * (algebraMap F K (π : F) ^ (k + c) * b) := by rw [hd, pow_add]; ring
      _ = f i j * algebraMap F K (π : F) ^ k * (v (i, j) : K) := by rw [← e]; ring
  · intro hv i j
    obtain ⟨b, hb, e⟩ := AddSubgroup.mem_addSubgroupOf.1 (hv (i, j) (Set.mem_univ _))
    replace e : d i j * b = (v (i, j) : K) := e
    refine ⟨algebraMap F K (π : F) ^ (k + c) * b, (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, rfl⟩, ?_⟩
    rw [scal_apply, ← e]
    calc f i j * (algebraMap F K (π : F) ^ k * (d i j * b))
        = (f i j * d i j) * (algebraMap F K (π : F) ^ k * b) := by ring
      _ = g i j * (algebraMap F K (π : F) ^ (k + c) * b) := by rw [hd, pow_add]; ring
end Formalism.HermitianLattices.Ext.L3.D2.NO
