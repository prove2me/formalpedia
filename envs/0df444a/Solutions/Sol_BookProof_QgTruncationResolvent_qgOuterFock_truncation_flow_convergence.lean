-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.qgOuterFock_truncation_flow_convergence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:28:15.52606+00:00
-- url     : https://prove2.me/submissions/66098fb5-a34b-4641-8fff-64cb527332b2

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_QgTruncationResolvent_esa_core_of_ext
import Theorems.Thm_BookProof_QgTruncationResolvent_strongResolventConvergence_of_core
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_tendstoUniformlyOn
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_tendsto
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
open BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.StoneBridge
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)
theorem solution (Λ : ℕ → Set ι)
    (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam W Q) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧
        StrongResolventConvergence T S ∧
        ∀ (v : Sec ι) (T₀ : ℝ), 0 ≤ T₀ →
          TendstoUniformlyOn (fun n t => (S n).stoneU t v) (fun t => T.stoneU t v) atTop
              (Set.Icc (-T₀) T₀) ∧
            ∀ t : ℝ, Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by
  classical
  have hdense : Dense ((secCore (ι := ι) : Submodule ℂ (Sec ι)) : Set (Sec ι)) :=
    BookProof.DirectSumEsa.dsCore_dense (fun _ => BookProof.ScalaronEsa.ccDomain_dense)
  have hesa : ∀ Q' : QgModeData ι, EssentiallySelfAdjointOn (secCore (ι := ι)) (secHam W Q') :=
    fun Q' => esa_core_of_ext (secData W Q') (secHam_essentiallySelfAdjointOn W Q')
  have hext : ∀ Q' : QgModeData ι, ∃ (Dom : Submodule ℂ (Sec ι)) (A : Dom →ₗ[ℂ] Sec ι),
      IsSelfAdjointExtension (secHam W Q') A :=
    fun Q' => exists_isSelfAdjointExtension_of_esa _ hdense (secHam_symmetricOn W Q') (hesa Q')
  choose Dom A hA using hext
  let T := unboundedSelfAdjointOf hdense (hA Q)
  let S : ℕ → UnboundedSelfAdjoint (Sec ι) := fun n => unboundedSelfAdjointOf hdense (hA (truncModes Q (Λ n)))
  have hconv : ∀ x : secCore (ι := ι),
      Tendsto (fun n => secHam W (truncModes Q (Λ n)) x) atTop (𝓝 (secHam W Q x)) := by
    intro x
    obtain ⟨P, hP1, -⟩ := exists_band Q x
    apply tendsto_const_nhds.congr'
    filter_upwards [hexh (P ∪ P.biUnion (fun b => Q.nbr b))] with n hn
    symm
    refine lp.ext (funext fun a => ?_)
    rw [secHam_apply, secHam_apply]
    simp only [truncModes_sig, truncModes_nbr]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl (fun b hb => ?_)
      by_cases hxb : (x : Sec ι) b = 0
      · rw [fibOf_eq_zero hxb]; simp
      · have hbP : b ∈ P := by by_contra h; exact hxb (hP1 b h)
        have ha : a ∈ P ∪ P.biUnion (fun b => Q.nbr b) :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hbP, (Q.mem_nbr_comm a b).mp hb⟩)
        simp [truncModes, hn a ha, hn b (Finset.mem_union_left _ hbP)]
    · refine Finset.sum_congr rfl (fun b hb => ?_)
      by_cases hxb : (x : Sec ι) b = 0
      · rw [fibOf_eq_zero hxb]; simp
      · have hbP : b ∈ P := by by_contra h; exact hxb (hP1 b h)
        have ha : a ∈ P ∪ P.biUnion (fun b => Q.nbr b) :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hbP, (Q.mem_nbr_comm a b).mp hb⟩)
        simp [truncModes, hn a ha, hn b (Finset.mem_union_left _ hbP)]
  have hres : StrongResolventConvergence T S :=
    strongResolventConvergence_of_core (hesa Q) (hA Q) (fun n => hA _) hconv
  exact ⟨T, S, hA Q, fun n => hA _, hres, fun v T₀ hT₀ =>
    ⟨trotterKato_tendstoUniformlyOn T S hres v hT₀, fun t => trotterKato_tendsto T S hres v t⟩⟩
