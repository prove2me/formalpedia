-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.span_singular_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:40.624743+00:00
-- url     : https://prove2.me/submissions/c0e3e873-6fda-4aae-a184-0afe864ffddb

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_le_Cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_Cl_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_Cl_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_mono_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_mem_MS
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_MS_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_MS_le_ker
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_etaK_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_exists_castSucc
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_top_of_stab
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_trace_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Formalism.FourierDecayAlt.P.ClosureOperators
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr ClosureOperators
private theorem MS_le_of_mem_of_invariant {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (f : Fin n → Module.End ℂ V)
    (v : V) (P : Submodule ℂ V) (hv : v ∈ P) (hf : ∀ x, ∀ q ∈ P, f x q ∈ P) : MS f v ≤ P := by
  have key : ∀ (k : ℕ) (g : Fin k → Module.End ℂ V), (∀ x, ∀ q ∈ P, g x q ∈ P) →
      ∀ b : Fin k → ℕ, mono g b v ∈ P := by
    intro k
    induction k with
    | zero =>
      intro g _ b
      have h1 : mono g b = 1 := by simp [mono]
      rw [h1]
      exact hv
    | succ k ih =>
      intro g hg b
      rw [mono_succ, Module.End.mul_apply]
      have h2 := ih (fun x => g x.succ) (fun x q hq => hg x.succ q hq) (fun x => b x.succ)
      generalize b 0 = j
      induction j with
      | zero => rw [pow_zero, Module.End.one_apply]; exact h2
      | succ j ihj => rw [pow_succ', Module.End.mul_apply]; exact hg 0 _ ihj
  unfold MS
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  exact key n f hf b
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr ClosureOperators
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.SpanSing := by
  intro V _ _ _ n E ξ₀ μ w hE hI hξ0 hlow hW hm
  by_contra hw
  obtain ⟨ζ, hζ⟩ := trace_scalar hE hI
  let M : Submodule ℂ V := MS (etaK E) w
  have hec : ∀ a b, etaK E a * etaK E b = etaK E b * etaK E a := etaK_comm hE
  have hwM : w ∈ M := mem_MS (etaK E) w
  have hMη : ∀ (x : Fin n), ∀ q ∈ M, E x.castSucc (Fin.last n) q ∈ M :=
    fun x q hq => MS_closed (etaK E) hec w x q hq
  have hw_up : ∀ a b : Fin (n + 1), a ≤ b → E a b w ∈ M := by
    intro a b hab
    by_cases hb : b = Fin.last n
    · subst hb
      by_cases ha : a = Fin.last n
      · subst ha
        have htr := hζ w
        rw [LinearMap.sum_apply, Fin.sum_univ_castSucc] at htr
        have hdiag : ∀ i : Fin n, E i.castSucc i.castSucc w = μ i • w := fun i => hW.1 i
        have hE' : E (Fin.last n) (Fin.last n) w = ζ • w - ∑ i : Fin n, μ i • w := by
          rw [← htr]
          simp only [hdiag]
          abel
        rw [hE']
        exact sub_mem (Submodule.smul_mem _ _ hwM) (sum_mem fun i _ => Submodule.smul_mem _ _ hwM)
      · obtain ⟨a', rfl⟩ := exists_castSucc a ha
        exact hMη a' w hwM
    · obtain ⟨b', rfl⟩ := exists_castSucc b hb
      have ha : a ≠ Fin.last n := by
        rintro rfl
        exact absurd hab (not_le.mpr (Fin.castSucc_lt_last b'))
      obtain ⟨a', rfl⟩ := exists_castSucc a ha
      rcases (Fin.castSucc_le_castSucc_iff.mp hab).lt_or_eq with h | h
      · rw [show E a'.castSucc b'.castSucc w = subA E a' b' w from rfl, hW.2 a' b' h]
        exact zero_mem _
      · subst h
        rw [show E a'.castSucc a'.castSucc w = subA E a' a' w from rfl, hW.1 a']
        exact Submodule.smul_mem _ _ hwM
  let N : Submodule ℂ V :=
    { carrier := {m | m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun a b h => by
        rw [map_add]; exact add_mem (hx.2 a b h) (hy.2 a b h)⟩
      zero_mem' := ⟨zero_mem _, fun a b _ => by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun a b h => by
        rw [map_smul]; exact Submodule.smul_mem _ c (hx.2 a b h)⟩ }
  have hNη : ∀ (x : Fin n), ∀ m ∈ N, etaK E x m ∈ N := by
    intro x m hm
    obtain ⟨hm1, hm2⟩ : m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M := hm
    refine ⟨hMη x m hm1, ?_⟩
    intro a b hab
    have hrel := LinearMap.congr_fun (hE a b x.castSucc (Fin.last n)) m
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hrel
    have key : E a b (etaK E x m) = E x.castSucc (Fin.last n) (E a b m) +
        ((if b = x.castSucc then E a (Fin.last n) else 0) m -
          (if Fin.last n = a then E x.castSucc b else 0) m) := by
      show E a b (E x.castSucc (Fin.last n) m) = _
      rw [sub_eq_iff_eq_add.mp hrel, add_comm]
    rw [key]
    refine add_mem (hMη x _ (hm2 a b hab)) (sub_mem ?_ ?_)
    · split_ifs with hb
      · exact hm2 a (Fin.last n) (Fin.le_last a)
      · rw [LinearMap.zero_apply]; exact zero_mem _
    · split_ifs with ha
      · subst ha
        have hb : b = Fin.last n := le_antisymm (Fin.le_last b) hab
        subst hb
        exact hm2 x.castSucc (Fin.last n) (Fin.le_last _)
      · rw [LinearMap.zero_apply]; exact zero_mem _
  have hwN : w ∈ N := ⟨hwM, hw_up⟩
  have hMN : M ≤ N := MS_le_of_mem_of_invariant (etaK E) w N hwN hNη
  let L : Fin (n + 1) → Fin (n + 1) → Prop := fun a b => b < a
  have hStab : Stab E (Cl E L M) := by
    intro a b q hq
    rcases lt_or_ge b a with hab | hab
    · exact Cl_closed a b hab q hq
    · refine gen hE (fun a b => a ≤ b) L M ?_ (fun a b c d _ _ _ => le_or_gt a d)
        (fun a b c d _ _ _ => le_or_gt c b) a b hab q hq
      intro a b h m hm'
      have h' : m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M := hMN hm'
      exact le_Cl E L M (h'.2 a b h)
  have htop := top_of_stab hI _ hStab w (le_Cl E L M hwM) hw
  apply hξ0
  have hker : Cl E L M ≤ LinearMap.ker ξ₀ := by
    apply Cl_le
    · exact MS_le_ker (etaK E) w ξ₀ hm
    · intro a b hab q _
      rw [LinearMap.mem_ker]
      exact hlow a b hab q
  ext v
  have hv : v ∈ Cl E L M := by rw [htop]; exact Submodule.mem_top
  rw [LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp (hker hv)
end Formalism.FourierDecayAlt.P
