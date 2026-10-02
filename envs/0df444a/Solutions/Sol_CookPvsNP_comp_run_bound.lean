-- Prove2me | solution 1 for CookPvsNP.comp_run_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:12:17.972129+00:00
-- url     : https://prove2.me/submissions/ed4707f4-afd6-4ef3-a53d-d9385ada5879

import Theorems.Thm_CookPvsNP_comp_setup_frame
import Theorems.Thm_CookPvsNP_comp_first_halt
import Theorems.Thm_CookPvsNP_comp_handoff
import Theorems.Thm_CookPvsNP_comp_second_halt
import Theorems.Thm_CookPvsNP_comp_cleanup
import Theorems.Thm_CookPvsNP_comp_cleanup_output
import Theorems.Thm_CookPvsNP_tm_run_tape_len

set_option autoImplicit false
open CookPvsNP

private theorem join {Γ : Type} (M : TM Γ) {a b : ℕ} {c d e : Cfg Γ M.Q}
    (h : M.run a c = d) (g : M.run b d = e) : M.run (a + b) c = e := by
  unfold TM.run at h g ⊢
  rw [Nat.add_comm, Function.iterate_add_apply, h]
  exact g

/-- The original composite machine computes the two finite source runs with linear overhead. -/
theorem solution {I S O A B : Type} [Fintype A] [Fintype B]
    (ι : I ↪ A) (j₁ : S ↪ A) (j₂ : S ↪ B) (κ : O ↪ B)
    (M₁ : TM A) (M₂ : TM B) (x : List I) (y : List S) (z : List O) (n₁ n₂ : ℕ)
    (h₁ : M₁.HaltsWithin n₁ (x.map ι))
    (o₁ : M₁.output (M₁.run n₁ (M₁.init (x.map ι))) = y.map (some ∘ j₁))
    (h₂ : M₂.HaltsWithin n₂ (y.map j₂))
    (o₂ : M₂.output (M₂.run n₂ (M₂.init (y.map j₂))) = z.map (some ∘ κ)) :
    ∃ t ≤ 20 * (x.length + n₁ + n₂ + 1),
      (compTM j₁ j₂ M₁ M₂).HaltsWithin t (x.map (compInputEmbedding ι)) ∧
      (compTM j₁ j₂ M₁ M₂).output
        ((compTM j₁ j₂ M₁ M₂).run t ((compTM j₁ j₂ M₁ M₂).init
          (x.map (compInputEmbedding ι)))) = z.map (some ∘ compOutputEmbedding κ) := by
  let C := compTM j₁ j₂ M₁ M₂
  let c := M₁.run n₁ (M₁.init (x.map ι))
  have hs := comp_setup_frame ι j₁ j₂ M₁ M₂ x
  obtain ⟨m₁, hm₁, hf⟩ := comp_first_halt j₁ j₂ M₁ M₂ (M₁.init (x.map ι)) n₁ h₁
  obtain ⟨d, hd, hds, hdr⟩ := comp_handoff j₁ j₂ M₁ M₂ c y h₁ o₁
  have hn₂ : M₂.IsHalting (M₂.run n₂ d.source) := by rw [hds]; exact h₂
  obtain ⟨m₂, hm₂, e, he, hes, her⟩ := comp_second_halt j₁ j₂ M₁ M₂ d n₂ hn₂
  have hen : M₂.IsHalting e.source := by rw [hes]; exact hn₂
  have heo : M₂.output e.source = z.map (some ∘ κ) := by rw [hes, hds]; exact o₂
  have hc := comp_cleanup j₁ j₂ M₁ M₂ e hen
  have hout := comp_cleanup_output j₁ j₂ κ M₁ M₂ e z heo
  let t := (((2 * max x.length 1 + 2) + 3 * m₁) + (2 * c.right.length + 6) +
    3 * m₂) + (2 * e.right.length + 4)
  have hrun : C.run t (C.init (x.map (compInputEmbedding ι))) = compCleanCfg e :=
    join C (join C (join C (join C hs hf) hd) he) hc
  have hr : c.right.length ≤ n₁ + x.length := by
    have h := tm_run_tape_len M₁ n₁ (M₁.init (x.map ι))
    change (M₁.run n₁ (M₁.init (x.map ι))).left.length + c.right.length ≤
      n₁ + (M₁.init (x.map ι)).left.length + (M₁.init (x.map ι)).right.length at h
    simp only [TM.init, List.length_nil, List.length_tail, List.length_map] at h
    dsimp only [c, TM.init] at h ⊢
    omega
  refine ⟨t, ?_, ?_, ?_⟩
  · have hmax : max x.length 1 ≤ x.length + 1 := by omega
    dsimp [t]
    omega
  · change C.IsHalting (C.run t (C.init (x.map (compInputEmbedding ι))))
    rw [hrun]
    exact Or.inl rfl
  · change C.output (C.run t (C.init (x.map (compInputEmbedding ι)))) = _
    rw [hrun]
    exact hout

#print axioms solution
