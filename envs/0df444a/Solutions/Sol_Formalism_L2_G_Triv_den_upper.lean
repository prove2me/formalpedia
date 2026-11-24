-- Prove2me | solution 1 for Formalism.L2.G.Triv.den_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:10.323788+00:00
-- url     : https://prove2.me/submissions/4be4f66b-defb-4fc1-a521-7ad6934b3d9f

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
import Theorems.Thm_Formalism_UG_P_adelstabL_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
variable {n : Type} [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n] [NumberField F] [Algebra F E]
namespace Formalism.L2.G.Triv
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) [Finite n] (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
  classical
  have := Fintype.ofFinite n
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  refine ⟨m, hm0, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
  | zero => intro k; simp [isIntegral_zero]
  | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
  | smul r x _ hx =>
    intro k
    have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
      simp [Algebra.smul_def]; ring
    rw [this]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
end Formalism.L2.G.Triv
