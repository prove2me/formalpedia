-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:47.390479+00:00
-- url     : https://prove2.me/submissions/c6a3562e-c909-4064-937e-74ce87cc0240

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace Formalism.UG.P
section FF
variable {𝔽 : Type} [Field 𝔽]
private theorem exists_linearIndependent_extension_fin (N : ℕ) (d k : ℕ) (hdk : d + k ≤ N) (v : Fin k → Fin N → 𝔽)
    (hv : LinearIndependent 𝔽 v) :
    ∃ s : Fin (d + k) → Fin N → 𝔽, LinearIndependent 𝔽 s ∧ ∀ i, s (Fin.natAdd d i) = v i := by
  induction d with
  | zero =>
    refine ⟨fun i => v (Fin.cast (Nat.zero_add k) i), hv.comp _ (Fin.cast_injective _), fun i => ?_⟩
    congr 1
    ext
    simp
  | succ d ih =>
    obtain ⟨s, hs, hsv⟩ := ih (by omega)
    obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank hs
      (by rw [Module.finrank_fin_fun]; omega)
    have hc : d + 1 + k = d + k + 1 := by omega
    refine ⟨fun i => (Fin.cons x s : Fin (d + k + 1) → Fin N → 𝔽) (Fin.cast hc i),
      hx.comp _ (Fin.cast_injective _), fun i => ?_⟩
    have e : Fin.cast hc (Fin.natAdd (d + 1) i) = Fin.succ (Fin.natAdd d i) := by
      ext
      simp only [Fin.coe_cast, Fin.coe_natAdd, Fin.val_succ]
      omega
    simp only [e, Fin.cons_succ]
    exact hsv i
end FF
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {𝔽 : Type} [Field 𝔽]
namespace Formalism.UG.P
theorem _root_.solution [Finite 𝔽] (n j : ℕ) (w : Fin (n - j) → Fin n → 𝔽)
    (hw : LinearIndependent 𝔽 w) :
    ∃ s : Fin n → Fin n → 𝔽, LinearIndependent 𝔽 s ∧ ∀ i, s (tjcosets_idx n j i) = w i := by
  obtain ⟨s, hs, hsw⟩ := exists_linearIndependent_extension_fin n (n - (n - j)) (n - j) (by omega) w hw
  have hc : n - (n - j) + (n - j) = n := by omega
  refine ⟨fun a => s (Fin.cast hc.symm a), hs.comp _ (Fin.cast_injective _), fun i => ?_⟩
  have e : Fin.cast hc.symm (tjcosets_idx n j i) = Fin.natAdd (n - (n - j)) i := by
    apply Fin.ext
    show j + (i : ℕ) = n - (n - j) + i
    have := i.isLt
    omega
  show s (Fin.cast hc.symm (tjcosets_idx n j i)) = w i
  rw [e, hsw]
end Formalism.UG.P
