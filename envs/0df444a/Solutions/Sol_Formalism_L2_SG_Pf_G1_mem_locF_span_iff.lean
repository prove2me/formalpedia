-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.mem_locF_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:33:54.050979+00:00
-- url     : https://prove2.me/submissions/f837088e-bbd5-459f-97ef-e31bee376794

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_div_mem_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_spanS
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_smul_mem_spanS
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_spanS_induction
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_mem_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locR_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_locF_eq_loc


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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {n : ℕ} (x : Fin n → V) (v : V) :
    v ∈ locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (Submodule.span (𝓞 K) (Set.range x)) ↔
      v ∈ spanS (locRing P) x := by
  rw [locF_eq_loc hK hF hP]
  have hPp := hP.isPrime
  constructor
  · intro hv
    change ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • v ∈ Submodule.span (𝓞 K) (Set.range x) at hv
    obtain ⟨s, hs, hsv⟩ := hv
    have h1 : s • v ∈ spanS (locRing P) x := by
      refine Submodule.span_induction (p := fun w _ => w ∈ spanS (locRing P) x) ?_ ?_ ?_ ?_ hsv
      · intro w hw
        obtain ⟨i, rfl⟩ := hw
        exact mem_spanS x i
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        exact Submodule.add_mem _ ha hb
      · intro c a _ ha
        rw [← algebraMap_smul K c a]
        exact smul_mem_spanS (algebraMap_mem_locRing P c) ha
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    have e : v = (algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K s) • (s • v) := by
      rw [← algebraMap_smul K s v, smul_smul, map_one, one_div, inv_mul_cancel₀ hs0, one_smul]
    rw [e]
    exact smul_mem_spanS (div_mem_locRing hPp 1 hs) h1
  · intro hv
    refine spanS_induction
      (p := fun w => ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • w ∈ Submodule.span (𝓞 K) (Set.range x))
      ⟨1, Submonoid.one_mem _, by rw [smul_zero]; exact Submodule.zero_mem _⟩ ?_ ?_ ?_ v hv
    · rintro a b ⟨s, hs, hsa⟩ ⟨t, ht, htb⟩
      refine ⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsa
      · rw [mul_smul]; exact Submodule.smul_mem _ _ htb
    · rintro c hc a ⟨s, hs, hsa⟩
      obtain ⟨r, s', hs', rfl⟩ := (mem_locR_iff hPp c).mp hc
      refine ⟨s' * s, Submonoid.mul_mem _ hs' hs, ?_⟩
      have hs'0 := algebraMap_ne_zero_of_mem_hcompl hPp hs'
      have e : (s' * s) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s') • a) = r • (s • a) := by
        rw [← algebraMap_smul K (s' * s), ← algebraMap_smul K r, ← algebraMap_smul K s, smul_smul,
          smul_smul, map_mul]
        congr 1
        field_simp
      rw [e]
      exact Submodule.smul_mem _ r hsa
    · intro i
      exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨i, rfl⟩⟩
end Formalism.L2.SG.Pf.G1
