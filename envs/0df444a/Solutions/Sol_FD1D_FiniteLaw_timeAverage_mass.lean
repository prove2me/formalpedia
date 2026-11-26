-- Prove2me | solution 1 for FD1D.FiniteLaw.timeAverage_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:28.528448+00:00
-- url     : https://prove2.me/submissions/6c5e6490-9290-4566-8970-d92475fe7441

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteLaw
theorem _root_.solution {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (t : Fin T) (x : α) :
    (timeAverage hT μ).mass (t, x) =
      (1 / (T : ℝ)) * (μ t).mass x :=
  rfl
end FD1D.FiniteLaw
