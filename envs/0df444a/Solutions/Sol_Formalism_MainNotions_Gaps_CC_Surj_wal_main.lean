-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.wal_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:51:03.340444+00:00
-- url     : https://prove2.me/submissions/1b81d662-0733-4b36-ad76-f7efc047facc

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_abs
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_sig_mem
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_delta
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_RatPtsLe
import Theorems.Thm_Formalism_UG_P_levelv_denom_family
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (h : WACore) : WeakApprox1 := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hθ hherm hdet Λ hfin hspan v g hg
  classical
  obtain ⟨m, hm0, hL⟩ := wal_delta (F := F) v Λ hfin hspan
  set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hι
  set Ji : Matrix n n (E ⊗[F] v.adicCompletion F) := (J⁻¹).map ι with hJidef
  obtain ⟨N, hN0, hN⟩ := Formalism.UG.P.levelv_denom_family (F := F) (E := E) v
    (Sum.elim (fun p : n × n =>
        ((g⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) p.1 p.2)
      (Sum.elim (fun p : n × n => (J.map ι) p.1 p.2) (fun p : n × n => Ji p.1 p.2)))
  have hD0 : (((N : ℤ) * (N : ℤ) * m : ℤ) : 𝓞 F) ≠ 0 :=
    Int.cast_ne_zero.2 (mul_ne_zero (mul_ne_zero (by exact_mod_cast hN0) (by exact_mod_cast hN0)) hm0)
  obtain ⟨γ, hγ, hs⟩ := h F E n σ J hσ hθ hherm hdet v g hg _ hD0
  choose T hT hTe using hs
  refine ⟨γ, hγ, ?_⟩
  have hγ' : bc ι γ ∈ UJ (sigR σ (v.adicCompletion F)) (J.map ι) :=
    Formalism.UG.Final.RatPtsLe F E n σ J (v.adicCompletion F) (Subgroup.mem_map_of_mem _ hγ)
  have hJi : Ji * J.map ι = 1 := by
    rw [hJidef, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one ι (map_zero ι) (map_one ι)]
  have hcS : ((N : ℕ) : E ⊗[F] v.adicCompletion F) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := natCast_mem _ N
  have hmS : ((m : ℤ) : E ⊗[F] v.adicCompletion F) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := intCast_mem _ m
  refine wal_abs _ (sigR σ (v.adicCompletion F)) (fun s hs => wal_sig_mem v σ hs) (J.map ι) Ji hJi _
    (m : E ⊗[F] v.adicCompletion F) (N : E ⊗[F] v.adicCompletion F) hmS hcS (map_intCast _ m)
    (map_natCast _ N) hL g (bc ι γ) hg hγ' ?_ ?_ ?_ (Matrix.of T) (fun i j => hT i j) ?_
  · intro i j
    have := hN (Sum.inl (i, j))
    rw [nsmul_eq_mul] at this
    exact this
  · intro i j
    have := hN (Sum.inr (Sum.inl (i, j)))
    rw [nsmul_eq_mul] at this
    exact this
  · intro i j
    have := hN (Sum.inr (Sum.inr (i, j)))
    rw [nsmul_eq_mul] at this
    exact this
  · ext i j
    have h1 := hTe i j
    have h2 : ι (algebraMap F E ((((N : ℤ) * (N : ℤ) * m : ℤ) : 𝓞 F) : F)) =
        (N : E ⊗[F] v.adicCompletion F) * (N : E ⊗[F] v.adicCompletion F) *
          (m : E ⊗[F] v.adicCompletion F) := by
      simp
    rw [h2] at h1
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← h1]
    rfl
end Formalism.MainNotions.Gaps.CC.Surj
