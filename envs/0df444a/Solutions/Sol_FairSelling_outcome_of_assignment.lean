-- Prove2me | solution 1 for FairSelling.outcome_of_assignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:34.382345+00:00
-- url     : https://prove2.me/submissions/5e542199-ad47-4f03-8947-d91e86c12dfb

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_outcome_of_bundles
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_fin3_cover
import Theorems.Thm_FairSelling_fin3_sum
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    {w : G → ℝ} {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ}
    {lo : Fin 3} (hcan : IsCanonical w p τ kept sold money lo)
    (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (kx ky kz : Fin 3) (hkxy : kx ≠ ky) (hkxz : kx ≠ kz) (hkyz : ky ≠ kz)
    (hx : (3 / 4 : ℝ) * MMS 3 (v x) p ≤ vbarSum (v x) p (kept kx) + money kx)
    (hy : (3 / 4 : ℝ) * MMS 3 (v y) p ≤ vbarSum (v y) p (kept ky) + money ky)
    (hz : (3 / 4 : ℝ) * MMS 3 (v z) p ≤ vbarSum (v z) p (kept kz) + money kz) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨hdisj, hsold, hm0, hmsum, -, -⟩ := hcan
  set ka : Fin 3 → Fin 3 := fun i => if i = x then kx else if i = y then ky else kz with hka
  have hkax : ka x = kx := by simp [hka]
  have hkay : ka y = ky := by simp [hka, (Ne.symm hxy)]
  have hkaz : ka z = kz := by simp [hka, (Ne.symm hxz), (Ne.symm hyz)]
  have hinj : ∀ i j, i ≠ j → ka i ≠ ka j := by
    intro i j hij
    rcases fin3_cover hxy hxz hyz i with hi | hi | hi <;>
      rcases fin3_cover hxy hxz hyz j with hj | hj | hj <;> subst hi <;> subst hj <;>
      simp_all [Ne.symm hkxy, Ne.symm hkxz, Ne.symm hkyz]
  refine outcome_of_bundles v p hp (fun i => kept (ka i)) sold (fun i => money (ka i))
    (fun i j hij => hdisj _ _ (hinj i j hij)) (fun i => hsold _) (fun i => hm0 _) ?_ ?_
  · have h1 : ∑ i, money (ka i) = money (ka x) + money (ka y) + money (ka z) :=
      fin3_sum hxy hxz hyz (fun i => money (ka i))
    have h2 : ∑ k, money k = money kx + money ky + money kz :=
      fin3_sum hkxy hkxz hkyz money
    rw [h1, hkax, hkay, hkaz, ← h2]
    exact hmsum
  · intro i
    rcases fin3_cover hxy hxz hyz i with hi | hi | hi <;> rw [hi]
    · simpa [hkax] using hx
    · simpa [hkay] using hy
    · simpa [hkaz] using hz
end FairSelling
