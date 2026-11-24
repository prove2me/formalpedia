-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.span_top_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:41.281331+00:00
-- url     : https://prove2.me/submissions/333faffb-bac5-4a33-a586-466774b0314b

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_yK_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_exists_castSucc
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_top_of_stab
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
theorem _root_.solution : Qr.SpanTop := by
  intro V _ _ n E ν v₀ hE hI hW hv0 ξ hξ hm
  let L : Fin (n + 1) → Fin (n + 1) → Prop := fun a b => a ≠ Fin.last n ∧ b ≠ Fin.last n ∧ b < a
  let M : Submodule ℂ V := MS (yK E) v₀
  have hyc : ∀ a b, yK E a * yK E b = yK E b * yK E a := yK_comm hE
  have hMC : M ≤ Cl E L M := le_Cl E L M
  have hv₀M : v₀ ∈ M := mem_MS (yK E) v₀
  have hNL : ∀ b, ¬ L (Fin.last n) b := fun b h => h.1 rfl
  have hY : ∀ (x : Fin n), ∀ q ∈ Cl E L M, E (Fin.last n) x.castSucc q ∈ Cl E L M := by
    intro x q hq
    refine gen hE (fun a b => a = Fin.last n ∧ b ≠ Fin.last n) L M ?_ ?_ ?_ _ _
      ⟨rfl, (Fin.castSucc_lt_last x).ne⟩ q hq
    · rintro a b ⟨rfl, hb⟩ m hm'
      obtain ⟨b', rfl⟩ := exists_castSucc b hb
      exact hMC (MS_closed (yK E) hyc v₀ b' m hm')
    · rintro a b c d ⟨ha, _⟩ ⟨_, hd, _⟩ _
      exact Or.inl ⟨ha, hd⟩
    · rintro a b c d ⟨ha, _⟩ ⟨_, hd, _⟩ hda
      exact absurd (hda.trans ha) hd
  let N : Submodule ℂ V :=
    { carrier := {m | m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun a b h => by
        rw [map_add]; exact add_mem (hx.2 a b h) (hy.2 a b h)⟩
      zero_mem' := ⟨zero_mem _, fun a b _ => by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun a b h => by
        rw [map_smul]; exact Submodule.smul_mem _ c (hx.2 a b h)⟩ }
  have hv₀N : v₀ ∈ N := by
    refine ⟨hMC hv₀M, ?_⟩
    intro a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · rw [hW.2 a b h]; exact zero_mem _
    · rw [hW.1 a]; exact Submodule.smul_mem _ _ (hMC hv₀M)
    · have ha : a = Fin.last n := by
        by_contra ha
        exact hab ⟨ha, ne_of_lt (lt_of_lt_of_le h (Fin.le_last a)), h⟩
      subst ha
      obtain ⟨b', rfl⟩ := exists_castSucc b (ne_of_lt h)
      exact hMC (MS_closed (yK E) hyc v₀ b' v₀ hv₀M)
  have hNy : ∀ (x : Fin n), ∀ m ∈ N, yK E x m ∈ N := by
    intro x m hm
    obtain ⟨hm1, hm2⟩ : m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M := hm
    refine ⟨hY x m hm1, ?_⟩
    intro a b hab
    have hrel := LinearMap.congr_fun (hE a b (Fin.last n) x.castSucc) m
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hrel
    have key : E a b (yK E x m) = E (Fin.last n) x.castSucc (E a b m) +
        ((if b = Fin.last n then E a x.castSucc else 0) m -
          (if x.castSucc = a then E (Fin.last n) b else 0) m) := by
      show E a b (E (Fin.last n) x.castSucc m) = _
      rw [sub_eq_iff_eq_add.mp hrel, add_comm]
    rw [key]
    refine add_mem (hY x _ (hm2 a b hab)) (sub_mem ?_ ?_)
    · split_ifs with hb
      · by_cases hL : L a x.castSucc
        · exact Cl_closed a x.castSucc hL m hm1
        · exact hm2 a x.castSucc hL
      · rw [LinearMap.zero_apply]; exact zero_mem _
    · split_ifs with hxa
      · exact hm2 (Fin.last n) b (hNL b)
      · rw [LinearMap.zero_apply]; exact zero_mem _
  have hMN : M ≤ N := MS_le_of_mem_of_invariant (yK E) v₀ N hv₀N hNy
  have hStab : Stab E (Cl E L M) := by
    intro a b q hq
    by_cases hab : L a b
    · exact Cl_closed a b hab q hq
    · refine gen hE (fun a b => ¬ L a b) L M ?_ (fun a b c d _ _ _ => (em (L a d)).symm)
        (fun a b c d _ _ _ => (em (L c b)).symm) a b hab q hq
      intro a b h m hm'
      have h' : m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M := hMN hm'
      exact h'.2 a b h
  have htop : Cl E L M = ⊤ := top_of_stab hI _ hStab v₀ (hMC hv₀M) hv0
  have hker : Cl E L M ≤ LinearMap.ker ξ := by
    apply Cl_le
    · exact MS_le_ker (yK E) v₀ ξ hm
    · intro a b hab q _
      obtain ⟨ha, hb, hba⟩ := hab
      obtain ⟨a', rfl⟩ := exists_castSucc a ha
      obtain ⟨b', rfl⟩ := exists_castSucc b hb
      rw [LinearMap.mem_ker]
      exact hξ a' b' (Fin.castSucc_lt_castSucc_iff.mp hba) q
  ext v
  have hv : v ∈ Cl E L M := by rw [htop]; exact Submodule.mem_top
  rw [LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp (hker hv)
end Formalism.FourierDecayAlt.P
