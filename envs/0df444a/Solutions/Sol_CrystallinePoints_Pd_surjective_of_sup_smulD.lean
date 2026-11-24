-- Prove2me | solution 1 for CrystallinePoints.Pd.surjective_of_sup_smulD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:30.877672+00:00
-- url     : https://prove2.me/submissions/ba5e8ccd-fb85-4c4a-b44a-16dc111582fd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoincareDeRhamDuality_DeRhamPerfectPairing_ResSurjD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct
open CrystallinePoints CrystallinePoints.Pd
namespace CrystallinePoints.Pd
theorem _root_.solution {R : Type} [CommRing R] {H M : Type*} [AddCommGroup H] [Module R H]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (γ : H →ₗ[R] M)
    (h : ∀ m : Ideal R, m.IsMaximal → LinearMap.range γ ⊔ m • (⊤ : Submodule R M) = ⊤) :
    Function.Surjective γ := by
  set P := LinearMap.range γ
  have key : ∀ m : Ideal R, m.IsMaximal → ∃ r : R, r - 1 ∈ m ∧ ∀ x : M, r • x ∈ P := by
    intro m hm
    have hin : (⊤ : Submodule R (M ⧸ P)) ≤ m • ⊤ := by
      have e := congrArg (Submodule.map P.mkQ) (h m hm)
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ,
        Submodule.mkQ_map_self, bot_sup_eq] at e
      exact e.symm.le
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _
      (Module.Finite.fg_top) hin
    refine ⟨r, hr, fun x ↦ ?_⟩
    have := hr' (Submodule.Quotient.mk x) trivial
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  let J : Ideal R :=
    { carrier := {r | ∀ x : M, r • x ∈ P}
      add_mem' := fun ha hb x ↦ by rw [add_smul]; exact P.add_mem (ha x) (hb x)
      zero_mem' := fun x ↦ by rw [zero_smul]; exact P.zero_mem
      smul_mem' := fun c r hr x ↦ by rw [smul_eq_mul, mul_smul]; exact P.smul_mem c (hr x) }
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨r, hr, hr'⟩ := key m hm
    have h1 : r ∈ m := hle hr'
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 hr))
  intro x
  have : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
  have hx : x ∈ P := by simpa using this x
  exact hx
end CrystallinePoints.Pd
