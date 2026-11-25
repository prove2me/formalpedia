-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.jet_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:50.435376+00:00
-- url     : https://prove2.me/submissions/e097e498-3b49-4410-86c2-5825e88293f6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_jet_iter
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP
variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (hD : DPullSt Y p) {n : ℕ} {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (co : ι → WVO I → C)
    (m : ι →₀ ℕ) (f : PS C n dd) :
    ∀ (ls : List ι), (∀ ℓ ∈ ls, m ℓ ≠ 0 → uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2) →
    ∀ q : MvPolynomial (Fin n × WVO I) C,
      jetAt0 q (pullN Y p (ls.foldr (fun l g => (DofN (Y.B.FK C) (cp l) (uv l))^[m l] g) f)) =
        jetAt0 (q * (ls.map fun l => (∑ w : WVO I, MvPolynomial.C (co l w) * MvPolynomial.X (cp l, w)) ^ m l).prod)
          (pullN Y p f) := by
  intro ls
  induction ls with
  | nil => intro _ q; simp
  | cons l ls ih =>
    intro hls q
    have htl : ∀ ℓ ∈ ls, m ℓ ≠ 0 → uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2 :=
      fun ℓ hℓ => hls ℓ (List.mem_cons_of_mem l hℓ)
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    by_cases hm : m l = 0
    · rw [hm, Function.iterate_zero, id, pow_zero, one_mul]
      exact ih htl q
    · rw [jet_iter hD (cp l) (uv l) (co l) (hls l List.mem_cons_self hm) (m l), ih htl, mul_assoc]
end Formalism.L2.FormalSeriesBounds.VP
