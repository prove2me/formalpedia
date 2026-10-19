-- Prove2me | solution 1 for BookProof.ChapterA.sup_JY_closure_isSubsystem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:26:06.427976+00:00
-- url     : https://prove2.me/submissions/e1aaf176-3b87-40ba-bd8e-4f62ba852027

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.sup_JY_closure_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1e
import Theorems.Thm_BookProof_ChapterA_JY_isSubsystem
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) {Y : Submodule ℝ V}
    (hY : (rxSystem M).IsSubsystem Y) :
    (rxSystem M).IsSubsystem (Y ⊔ JY Y).topologicalClosure := by

  refine ⟨ isClosed_closure, ?_ ⟩;
  intro m hm w hw
  have h_maps_to : ∀ w ∈ Y ⊔ JY Y, m w ∈ Y ⊔ JY Y := by
    intro w hw
    have h_maps_to : ∀ y ∈ Y, m y ∈ Y := by
      exact hY.2 m hm
    have h_maps_to_JY : ∀ y ∈ JY Y, m y ∈ JY Y := by
      have := JY_isSubsystem M hY;
      exact this.2 m hm;
    rw [ Submodule.mem_sup ] at hw ⊢;
    rcases hw with ⟨ y, hy, z, hz, rfl ⟩ ;      exact ⟨ m y, h_maps_to y hy, m z, h_maps_to_JY z hz,
        by simp [ map_add ] ⟩ ;
  exact mem_closure_of_tendsto ( m.continuous.continuousAt.tendsto.comp ( show Filter.Tendsto ( fun
      n : ℕ => Classical.choose ( mem_closure_iff_seq_limit.mp hw ) n ) Filter.atTop ( nhds w ) from
          Classical.choose_spec ( mem_closure_iff_seq_limit.mp hw ) |>.2 ) ) (
              Filter.Eventually.of_forall fun n => h_maps_to _ ( Classical.choose_spec (
                  mem_closure_iff_seq_limit.mp hw ) |>.1 n ) )
