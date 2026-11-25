-- Prove2me | solution 1 for CompanionTheory.CapEig.word_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:45.587843+00:00
-- url     : https://prove2.me/submissions/c0ed713b-4ff4-496c-8ed5-4bcd55c571f1

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Theorems.Thm_CompanionTheory_CapEig_eab_vec
import Theorems.Thm_Formalism_QuantumDeterminants_ioE_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_mem_smooth
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}
namespace CompanionTheory.CapEig
theorem _root_.solution (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs} {x : ioS ε Hs}
    (hx : IORep (fun y => σ y v) x.1) : ∀ w : List (Fin n × Fin n),
    IORep (fun y => σ y (dsigCW ε σ (w.map unitM) v)) ((w.map fun ab => ioE ε Hs ab.1 ab.2).prod x).1
  | [] => by simpa [dsigCW] using hx
  | ab :: w => by
    have ih := solution hm hx w
    have hs : SmoothOnGV ε fun y => σ y (dsigCW ε σ (w.map unitM) v) :=
      io_smooth_congr (fun g hg => (io_rep_ext _ g hg).trans (ih g hg).symm) (io_mem_smooth _)
    intro g hg
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, dsigCW]
    rw [← ioE_rep ih ab.1 ab.2 g hg, eab_vec hm hs ab.1 ab.2 hg]
end CompanionTheory.CapEig
